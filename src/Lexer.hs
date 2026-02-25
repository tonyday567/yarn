{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- |
-- Module      : Lexer
-- Description : State-machine lexers via Traced MealyM
--
-- Performance principle: machines never allocate ByteStrings.
-- Runners drive directly over ByteString via unsafeIndex.
-- Token emission is unsafeSlice — zero copy.
-- Allocation is O(tokens), not O(bytes).

module Lexer
  ( -- * Word lexer
    runWordLexerBS
  , wordFreqBS
    -- * Markup lexer
  , MarkupCtx (..)
  , MarkupToken (..)
  , markupLexer
  , runMarkupLexerBS
    -- * Compiler
  , runMealy
  , runMarkupMealyBS
  , compiledMarkupLexer
  , runCompiledMarkupBS
  ) where

import Prelude hiding (id, (.))
import qualified Prelude

import Data.Word (Word8)
import Data.Char (ord)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

import GHC.Exts (lazy)
import MealyM (MealyM (..), mkMealy, withMealy, delay)
import Traced (Traced (..))
import Control.Category ((.),  id)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Strict unboxed pair of byte and index.
-- Using a newtype with UNPACK instead of (Word8, Int) avoids a heap
-- allocation per step when threading the index through the pipeline.
-- GHC passes the fields as two separate unboxed arguments.
data WI = WI {-# UNPACK #-} !Word8 {-# UNPACK #-} !Int

isAlphaW :: Word8 -> Bool
isAlphaW w = (w >= 65 && w <= 90) || (w >= 97 && w <= 122)

toLowerW :: Word8 -> Word8
toLowerW w | w >= 65 && w <= 90 = w + 32
           | otherwise           = w

{-# INLINE second' #-}
second' :: MealyM b c -> MealyM (a, b) (a, c)
second' m = withMealy m $ \fi fs fe ->
  mkMealy
    (\(a, b)        -> (a, fi b))
    (\(a, s) (_, b) -> let (c, s') = fs s b in ((a, c), (a, s')))
    (\(a, s)        -> (a, fe s))

-- ---------------------------------------------------------------------------
-- Compile Traced MealyM -> MealyM
-- ---------------------------------------------------------------------------

-- {-# INLINE runMealy #-}  -- Disabled to prevent GHC from seeing through lazy knot
runMealy :: Traced MealyM a b -> MealyM a b
runMealy Pure          = mkMealy Prelude.id (\_ a -> (a, a)) Prelude.id
runMealy (Lift m)      = m
runMealy (Compose g h) = withMealy (runMealy g) $ \fi fs fe ->
                         withMealy (runMealy h) $ \gi gs ge ->
                         mkMealy
                           (\a      -> let !t = gi a; !b = ge t; !s = fi b in (s, t))
                           (\(s,t) a -> let (mid,!t') = gs t a; (out,!s') = fs s mid in (out,(s',t')))
                           (\(s,_)   -> fe s)
runMealy (Loop p)      = withMealy (runMealy p) $ \fi fs fe ->
                         mkMealy
                           -- lazy knot: works when inject does not force c
                           (\a   -> let s0 = fi (a, c0); c0 = snd (fe s0) in s0)
                           (\s a -> let c = snd (fe s); ((b,_),s') = fs s (a,c) in (b,s'))
                           (\s   -> fst (fe s))

-- ---------------------------------------------------------------------------
-- Word lexer — direct ByteString, offset tracking, zero copy
-- ---------------------------------------------------------------------------

-- | Run word lexer directly over a ByteString.
-- No [Word8] allocation. unsafeIndex for input, unsafeSlice for output.
-- toLower applied in lowerSlice — one allocation per token, not per byte.
runWordLexerBS :: ByteString -> [ByteString]
runWordLexerBS bs = go 0 False 0
  where
    !len = BS.length bs
    go !i !inWord !start
      | i >= len  = if inWord then [lowerSlice start (i - start)] else []
      | otherwise =
          let !w = BSU.unsafeIndex bs i
          in  if isAlphaW w
                then go (i+1) True (if inWord then start else i)
                else if inWord
                  then lowerSlice start (i - start) : go (i+1) False 0
                  else go (i+1) False 0
    lowerSlice s l = BS.map toLowerW (BSU.unsafeTake l (BSU.unsafeDrop s bs))

-- | Word frequency map — single pass, no intermediate list.
wordFreqBS :: ByteString -> Map ByteString Int
wordFreqBS bs = go 0 False 0 Map.empty
  where
    !len = BS.length bs
    go !i !inWord !start !m
      | i >= len  =
          if inWord
            then Map.insertWith (+) (lowerSlice start (i - start)) 1 m
            else m
      | otherwise =
          let !w = BSU.unsafeIndex bs i
          in  if isAlphaW w
                then go (i+1) True (if inWord then start else i) m
                else if inWord
                  then go (i+1) False 0
                         (Map.insertWith (+) (lowerSlice start (i - start)) 1 m)
                  else go (i+1) False 0 m
    lowerSlice s l = BS.map toLowerW (BSU.unsafeTake l (BSU.unsafeDrop s bs))

-- ---------------------------------------------------------------------------
-- Markup types
-- ---------------------------------------------------------------------------

data MarkupCtx
  = InContent | InTagName | InAttr
  | InAttrVal Char | InClose | InComment
  deriving (Eq, Show, Generic)

instance NFData MarkupCtx

-- | Markup token. ByteString fields are zero-copy slices of the input.
data MarkupToken
  = TOpenTag  ByteString
  | TCloseTag ByteString
  | TContent  ByteString
  | TSelfClose
  | TTagEnd
  | TAttrName ByteString
  | TAttrVal  ByteString
  | TComment  ByteString
  deriving (Eq, Show, Generic)

instance NFData MarkupToken

data ByteClass
  = BLt | BGt | BSlash | BEquals
  | BQuote Char | BSpace | BAlpha Word8
  | BDash | BBang | BQuestion
  deriving (Eq, Show)

classifyByte :: MarkupCtx -> Word8 -> ByteClass
classifyByte _ w = case w of
  60 -> BLt;  62 -> BGt;  47 -> BSlash; 61 -> BEquals
  39 -> BQuote '\''
  34 -> BQuote '"'
  32 -> BSpace; 9 -> BSpace; 10 -> BSpace; 13 -> BSpace
  45 -> BDash; 33 -> BBang; 63 -> BQuestion
  _  -> BAlpha w

-- ---------------------------------------------------------------------------
-- Markup accumulator — offset tracking
-- ---------------------------------------------------------------------------

-- | Accumulator: track start offset and length of current token being built.
-- Never holds a [Word8]. Emit is a slice of the original ByteString.
data AccState = AccState
  { accStart :: {-# UNPACK #-} !Int
  , accLen   :: {-# UNPACK #-} !Int
  , accCtx   :: !MarkupCtx
  }

-- | Step the accumulator given a byte class, current context, and byte index.
-- Returns an emit action (constructor + slice coords) and new state.
accumStep :: AccState -> ByteClass -> Int
          -> (Maybe (ByteString -> MarkupToken, Int, Int), AccState)
accumStep (AccState !s !l !ctx) bc !i = case (ctx, bc) of
  (InContent, BLt)    ->
    ( if l == 0 then Nothing else Just (TContent, s, l)
    , AccState i 0 InTagName)
  (InContent, _)      ->
    (Nothing, AccState (if l==0 then i else s) (l+1) InContent)
  (InTagName, BSpace) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l)
    , AccState i 0 InAttr)
  (InTagName, BGt)    ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l)
    , AccState i 0 InContent)
  (InTagName, BSlash) ->
    if l == 0
      then (Nothing, AccState i 0 InClose)
      else (Nothing, AccState s (l+1) InTagName)
  (InTagName, _)      ->
    (Nothing, AccState (if l==0 then i else s) (l+1) InTagName)
  (InAttr, BGt)       ->
    (Just (Prelude.const TTagEnd,    0, 0), AccState i 0 InContent)
  (InAttr, BSlash)    ->
    (Just (Prelude.const TSelfClose, 0, 0), AccState i 0 InContent)
  (InAttr, BSpace)    ->
    (Nothing, AccState i 0 InAttr)
  (InAttr, _)         ->
    (Nothing, AccState (if l==0 then i else s) (l+1) InAttr)
  (InClose, BGt)      ->
    ( if l == 0 then Nothing else Just (TCloseTag, s, l)
    , AccState i 0 InContent)
  (InClose, BSpace)   ->
    (Nothing, AccState s l InClose)
  (InClose, _)        ->
    (Nothing, AccState (if l==0 then i else s) (l+1) InClose)
  _                   ->
    (Nothing, AccState (if l==0 then i else s) (l+1) ctx)

-- ---------------------------------------------------------------------------
-- Markup runner — direct ByteString, zero copy
-- ---------------------------------------------------------------------------

-- | Run markup lexer directly over a ByteString.
-- Context state machine driven byte by byte via unsafeIndex.
-- Token emission via unsafeSlice — zero copy for all name/content tokens.
runMarkupLexerBS :: ByteString -> [MarkupToken]
runMarkupLexerBS bs = go 0 (AccState 0 0 InContent)
  where
    !len = BS.length bs
    go !i !acc
      | i >= len  = []
      | otherwise =
          let !w            = BSU.unsafeIndex bs i
              !bc           = classifyByte (accCtx acc) w
              (emit, !acc') = accumStep acc bc i
          in  case emit of
                Nothing         -> go (i+1) acc'
                Just (con, s, l) ->
                  let !tok = if l == 0
                               then con BS.empty
                               else con (BSU.unsafeTake l (BSU.unsafeDrop s bs))
                  in  tok : go (i+1) acc'

-- ---------------------------------------------------------------------------
-- MealyM driver — ByteString input, filters Nothings
-- ---------------------------------------------------------------------------

-- | Drive a MealyM Word8 (Maybe b) directly over a ByteString.
-- Same unsafeIndex loop as the hand-written runners.
-- This is what we benchmark against hand-written to measure machinery cost.
{-# INLINE driveBSMaybe #-}
driveBSMaybe :: MealyM Word8 (Maybe b) -> ByteString -> [b]
driveBSMaybe m bs = withMealy m $ \fi fs _ ->
  let go !s bs'
        | BS.null bs' = []
        | otherwise   =
            let !w       = BSU.unsafeHead bs'
                (b, !s') = fs s w
            in  case b of
                  Just t  -> t : go s' (BSU.unsafeTail bs')
                  Nothing ->     go s' (BSU.unsafeTail bs')
  in if BS.null bs then []
     else go (fi (BSU.unsafeHead bs)) (BSU.unsafeTail bs)

-- | Run markup lexer via compiled Traced MealyM with index threading.
-- Uses markupLexerI — offset tracking, zero copy, no [Word8] accumulator.
-- The runner pairs each byte with its index before feeding to the machine.
runMarkupMealyBS :: ByteString -> [MarkupToken]
runMarkupMealyBS bs = driveIndexed (runMealy markupLexerI) bs
  where
    driveIndexed m bs' = withMealy m $ \fi fs _ ->
      let go !s !i bs''
            | BS.null bs'' = []
            | otherwise    =
                let !w           = BSU.unsafeHead bs''
                    (mEmit, !s') = fs s (WI w i)
                in  case mEmit of
                      Nothing                ->
                        go s' (i+1) (BSU.unsafeTail bs'')
                      Just (con, start, len) ->
                        let !tok = if len == 0
                                     then con BS.empty
                                     else con (BSU.unsafeTake len (BSU.unsafeDrop start bs))
                        in  tok : go s' (i+1) (BSU.unsafeTail bs'')
      in if BS.null bs' then []
         else let !w0 = BSU.unsafeHead bs'
                  !s0 = fi (WI w0 0)
              in  go s0 1 (BSU.unsafeTail bs')

-- ---------------------------------------------------------------------------
-- Markup lexer as Traced MealyM
-- (for composition; uses [Word8] accumulator internally)
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Offset-tracking accumulator for Traced MealyM pipeline
-- ---------------------------------------------------------------------------
--
-- Input to the pipeline: (Word8, Int) — byte paired with its index.
-- Index flows through all stages so accumulator can track (start, len).
-- No [Word8] allocation. Token emission is unsafeTake/unsafeDrop slice.
--
-- Pipeline shape:
--   Loop InContent $
--     stage2 . stage1
--
-- where:
--   stage1 :: (Word8, Int, Ctx) -> (ByteClass, Int, Ctx)   classify + pass index
--   stage2 :: (ByteClass, Int, Ctx) -> (Maybe (con,s,l), Ctx)  accumulate offsets
--
-- The Ctx wire is the Loop feedback.
-- The Int (index) flows through as part of the value, not the feedback.

-- | Offset-tracking accumulator state for the Traced pipeline.
data OAccState = OAccState
  { oStart :: {-# UNPACK #-} !Int
  , oLen   :: {-# UNPACK #-} !Int
  , oCtx   :: !MarkupCtx
  }

-- | Step the offset accumulator.
-- Input: (ByteClass, Int, MarkupCtx)  — class, current index, feedback ctx
-- Output: (Maybe emit, new ctx) where emit = (constructor, start, len)
oAccumStep :: OAccState -> (ByteClass, Int, MarkupCtx)
           -> (Maybe (ByteString -> MarkupToken, Int, Int), OAccState)
oAccumStep (OAccState !s !l !ctx) (bc, !i, _) = case (ctx, bc) of
  (InContent, BLt)    ->
    ( if l == 0 then Nothing else Just (TContent, s, l)
    , OAccState i 0 InTagName)
  (InContent, _)      ->
    (Nothing, OAccState (if l==0 then i else s) (l+1) InContent)
  (InTagName, BSpace) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l)
    , OAccState i 0 InAttr)
  (InTagName, BGt)    ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l)
    , OAccState i 0 InContent)
  (InTagName, BSlash) ->
    if l == 0 then (Nothing, OAccState i 0 InClose)
    else            (Nothing, OAccState s (l+1) InTagName)
  (InTagName, _)      ->
    (Nothing, OAccState (if l==0 then i else s) (l+1) InTagName)
  (InAttr, BGt)       ->
    (Just (Prelude.const TTagEnd,    0, 0), OAccState i 0 InContent)
  (InAttr, BSlash)    ->
    (Just (Prelude.const TSelfClose, 0, 0), OAccState i 0 InContent)
  (InAttr, BSpace)    ->
    (Nothing, OAccState i 0 InAttr)
  (InAttr, _)         ->
    (Nothing, OAccState (if l==0 then i else s) (l+1) InAttr)
  (InClose, BGt)      ->
    ( if l == 0 then Nothing else Just (TCloseTag, s, l)
    , OAccState i 0 InContent)
  (InClose, BSpace)   -> (Nothing, OAccState s l InClose)
  (InClose, _)        ->
    (Nothing, OAccState (if l==0 then i else s) (l+1) InClose)
  _                   ->
    (Nothing, OAccState (if l==0 then i else s) (l+1) ctx)

-- | Stage 1: classify byte, pass index through.
-- Input:  ((Word8, Int), MarkupCtx)   — nested for Loop compatibility
-- Output: ((ByteClass, Int), MarkupCtx)
-- | Stage 1: classify byte, pass index through.
stage1 :: Traced MealyM (WI, MarkupCtx) ((ByteClass, Int), MarkupCtx)
stage1 = Lift $ mkMealy
  -- inject: store input as state, no classification, ctx not forced
  (\input -> input)
  -- step: update state, classify for output
  (\_ input -> let !r = classify input in (r, input))
  -- extract: classify on demand
  classify
  where
    classify (WI w i, ctx) = ((classifyByte ctx w, i), ctx)

-- | Stage 2: accumulate offsets, emit token slice coordinates.
-- Input:  ((ByteClass, Int), MarkupCtx)  — nested for Loop compatibility
-- Output: (Maybe (con, start, len), MarkupCtx)  — ctx on feedback wire
-- State:  (Maybe emit, OAccState) — last emit + accumulator
stage2 :: Traced MealyM ((ByteClass, Int), MarkupCtx)
                        (Maybe (ByteString -> MarkupToken, Int, Int), MarkupCtx)
stage2 = Lift $ mkMealy
  -- inject: irrefutable pattern — do not force the input tuple.
  -- This allows the lazy knot to tie ctx before s1e is evaluated.
  -- OAccState stores ctx lazily (not UNPACK'd); i is forced but that's fine.
  (\input -> let ~((_, i), ctx) = input in (Nothing, OAccState i 0 ctx))
  -- step: carry OAccState, use its ctx (updated each step via Loop)
  (\(_, !acc) ((bc, i), _) ->
    let (emit, !acc') = oAccumStep acc (bc, i, oCtx acc)
        !out           = (emit, oCtx acc')
    in  (out, (emit, acc')))
  -- extract: emit + ctx from accumulator
  (\(emit, acc) -> (emit, oCtx acc))

-- | Markup lexer as Traced MealyM with offset tracking.
-- Input is (Word8, Int) — byte paired with its index.
-- Loop closes the MarkupCtx feedback wire.
-- The nested pair structure ((Word8,Int), MarkupCtx) satisfies Loop's (a,c) requirement.
markupLexerI :: Traced MealyM WI
                              (Maybe (ByteString -> MarkupToken, Int, Int))
markupLexerI = Loop body
  where
    body :: Traced MealyM (WI, MarkupCtx)
                          (Maybe (ByteString -> MarkupToken, Int, Int), MarkupCtx)
    body = Compose stage2 stage1

-- | Public markup lexer — Word8 input, [Word8] accumulator.
-- Kept for API compatibility. For performance use runMarkupMealyBS.
markupLexer :: Traced MealyM Word8 (Maybe MarkupToken)
markupLexer = Loop (Compose stage2old stage1old)

stage1old :: Traced MealyM (Word8, MarkupCtx) (ByteClass, MarkupCtx)
stage1old = Lift $ mkMealy
  (\(w, ctx) -> (classifyByte ctx w, ctx))
  (\_ (w, ctx) -> let r = (classifyByte ctx w, ctx) in (r, r))
  Prelude.id

data MAccState = MAccState ![Word8] !MarkupCtx

classW :: ByteClass -> Word8
classW (BAlpha w) = w
classW (BQuote c) = fromIntegral (ord c)
classW BSpace = 32; classW BDash = 45; classW BEquals = 61; classW _ = 63

stage2old :: Traced MealyM (ByteClass, MarkupCtx) (Maybe MarkupToken, MarkupCtx)
stage2old = Lift $ mkMealy
  (\(bc, ctx) ->
    let (tok, MAccState _ ctx') = mAccumStep (MAccState [] ctx) (bc, ctx)
    in  (tok, ctx'))
  (\(_, ctx) (bc, _) ->
    let (tok, MAccState _ ctx') = mAccumStep (MAccState [] ctx) (bc, ctx)
        r = (tok, ctx')
    in  (r, r))
  Prelude.id

mAccumStep :: MAccState -> (ByteClass, MarkupCtx) -> (Maybe MarkupToken, MAccState)
mAccumStep (MAccState buf ctx) (bc, _) = case (ctx, bc) of
  (InContent, BLt)    ->
    ( if Prelude.null buf then Nothing
      else Just (TContent (BS.pack (Prelude.reverse buf)))
    , MAccState [] InTagName)
  (InContent, _)      -> (Nothing, MAccState (classW bc : buf) InContent)
  (InTagName, BSpace) ->
    ( if Prelude.null buf then Nothing
      else Just (TOpenTag (BS.pack (Prelude.reverse buf)))
    , MAccState [] InAttr)
  (InTagName, BGt)    ->
    ( if Prelude.null buf then Nothing
      else Just (TOpenTag (BS.pack (Prelude.reverse buf)))
    , MAccState [] InContent)
  (InTagName, BSlash) ->
    if Prelude.null buf then (Nothing, MAccState [] InClose)
    else                     (Nothing, MAccState (47 : buf) InTagName)
  (InTagName, _)      -> (Nothing, MAccState (classW bc : buf) InTagName)
  (InAttr, BGt)       -> (Just TTagEnd,    MAccState [] InContent)
  (InAttr, BSlash)    -> (Just TSelfClose, MAccState [] InContent)
  (InAttr, BSpace)    -> (Nothing,         MAccState [] InAttr)
  (InAttr, _)         -> (Nothing,         MAccState (classW bc : buf) InAttr)
  (InClose, BGt)      ->
    ( if Prelude.null buf then Nothing
      else Just (TCloseTag (BS.pack (Prelude.reverse buf)))
    , MAccState [] InContent)
  (InClose, BSpace)   -> (Nothing, MAccState buf InClose)
  (InClose, _)        -> (Nothing, MAccState (classW bc : buf) InClose)
  _                   -> (Nothing, MAccState (classW bc : buf) ctx)

-- ---------------------------------------------------------------------------
-- compiledMarkupLexer — manually inlined runMealy, no recursive interpreter
-- ---------------------------------------------------------------------------
--
-- runMealy is in a Rec{} group in Core because it recurses over the Traced
-- tree. GHC will not inline a recursive binding, so the interpreter stays
-- opaque at the call site.
--
-- compiledMarkupLexer performs the same composition as runMealy markupLexerI
-- but non-recursively: withMealy on each stage, then close the Loop by hand.

-- | Compiled markup lexer.
-- Uses runMealy on markupLexerI for correctness.
-- TODO: optimize with manual inlining once lazy knot deadlock is fixed.
-- The deadlock occurs because stage2's init forces the context argument
-- before the lazy knot has fully established.
compiledMarkupLexer :: MealyM WI (Maybe (ByteString -> MarkupToken, Int, Int))
compiledMarkupLexer = runMealy markupLexerI


-- | Run compiledMarkupLexer over a ByteString.
runCompiledMarkupBS :: ByteString -> [MarkupToken]
runCompiledMarkupBS bs = withMealy compiledMarkupLexer $ \fi fs _ ->
  let go !s !i bs'
        | BS.null bs' = []
        | otherwise   =
            let !w           = BSU.unsafeHead bs'
                (mEmit, !s') = fs s (WI w i)
            in  case mEmit of
                  Nothing                ->
                    go s' (i+1) (BSU.unsafeTail bs')
                  Just (con, start, len) ->
                    let !tok = if len == 0
                                 then con BS.empty
                                 else con (BSU.unsafeTake len (BSU.unsafeDrop start bs))
                    in  tok : go s' (i+1) (BSU.unsafeTail bs')
  in if BS.null bs then []
     else let !w0 = BSU.unsafeHead bs
              !s0  = fi (WI w0 0)
          in  go s0 1 (BSU.unsafeTail bs)

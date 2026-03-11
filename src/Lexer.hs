{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
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
    runWordLexerBS,
    wordFreqBS,

    -- * Markup lexer
    MarkupCtx (..),
    MarkupToken (..),
    runMarkupLexerBS,

    -- * Traced (->) State pipeline
    runMarkupStateBS,
    WI (..),
    AccState (..),
    classifyByte,
    accumStep,
    ByteClass (..),
    initOAccState,
  )
where

import Control.Category (id, (.))
import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSU
import Data.Char (ord)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Word (Word8)
import GHC.Exts (lazy)
import GHC.Generics (Generic)
import Traced (Traced (..), run)
import Prelude hiding (id, (.))
import Prelude qualified

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
toLowerW w
  | w >= 65 && w <= 90 = w + 32
  | otherwise = w

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
      | i >= len = if inWord then [lowerSlice start (i - start)] else []
      | otherwise =
          let !w = BSU.unsafeIndex bs i
           in if isAlphaW w
                then go (i + 1) True (if inWord then start else i)
                else
                  if inWord
                    then lowerSlice start (i - start) : go (i + 1) False 0
                    else go (i + 1) False 0
    lowerSlice s l = BS.map toLowerW (BSU.unsafeTake l (BSU.unsafeDrop s bs))

-- | Word frequency map — single pass, no intermediate list.
wordFreqBS :: ByteString -> Map ByteString Int
wordFreqBS bs = go 0 False 0 Map.empty
  where
    !len = BS.length bs
    go !i !inWord !start !m
      | i >= len =
          if inWord
            then Map.insertWith (+) (lowerSlice start (i - start)) 1 m
            else m
      | otherwise =
          let !w = BSU.unsafeIndex bs i
           in if isAlphaW w
                then go (i + 1) True (if inWord then start else i) m
                else
                  if inWord
                    then
                      go
                        (i + 1)
                        False
                        0
                        (Map.insertWith (+) (lowerSlice start (i - start)) 1 m)
                    else go (i + 1) False 0 m
    lowerSlice s l = BS.map toLowerW (BSU.unsafeTake l (BSU.unsafeDrop s bs))

-- ---------------------------------------------------------------------------
-- Markup types
-- ---------------------------------------------------------------------------

data MarkupCtx
  = InContent
  | InTagName
  | InAttr
  | InAttrVal Char
  | InClose
  | InComment
  deriving (Eq, Show, Generic)

instance NFData MarkupCtx

-- | Markup token. ByteString fields are zero-copy slices of the input.
data MarkupToken
  = TOpenTag ByteString
  | TCloseTag ByteString
  | TContent ByteString
  | TSelfClose
  | TTagEnd
  | TAttrName ByteString
  | TAttrVal ByteString
  | TComment ByteString
  deriving (Eq, Show, Generic)

instance NFData MarkupToken

data ByteClass
  = BLt
  | BGt
  | BSlash
  | BEquals
  | BQuote Char
  | BSpace
  | BAlpha Word8
  | BDash
  | BBang
  | BQuestion
  deriving (Eq, Show)

classifyByte :: MarkupCtx -> Word8 -> ByteClass
classifyByte _ w = case w of
  60 -> BLt
  62 -> BGt
  47 -> BSlash
  61 -> BEquals
  39 -> BQuote '\''
  34 -> BQuote '"'
  32 -> BSpace
  9 -> BSpace
  10 -> BSpace
  13 -> BSpace
  45 -> BDash
  33 -> BBang
  63 -> BQuestion
  _ -> BAlpha w

-- ---------------------------------------------------------------------------
-- Markup accumulator — offset tracking
-- ---------------------------------------------------------------------------

-- | Accumulator: track start offset and length of current token being built.
-- Never holds a [Word8]. Emit is a slice of the original ByteString.
data AccState = AccState
  { accStart :: {-# UNPACK #-} !Int,
    accLen :: {-# UNPACK #-} !Int,
    accCtx :: !MarkupCtx
  }

-- | Step the accumulator given a byte class, current context, and byte index.
-- Returns an emit action (constructor + slice coords) and new state.
accumStep ::
  AccState ->
  ByteClass ->
  Int ->
  (Maybe (ByteString -> MarkupToken, Int, Int), AccState)
accumStep (AccState !s !l !ctx) bc !i = case (ctx, bc) of
  (InContent, BLt) ->
    ( if l == 0 then Nothing else Just (TContent, s, l),
      AccState i 0 InTagName
    )
  (InContent, _) ->
    (Nothing, AccState (if l == 0 then i else s) (l + 1) InContent)
  (InTagName, BSpace) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l),
      AccState i 0 InAttr
    )
  (InTagName, BGt) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l),
      AccState i 0 InContent
    )
  (InTagName, BSlash) ->
    if l == 0
      then (Nothing, AccState i 0 InClose)
      else (Nothing, AccState s (l + 1) InTagName)
  (InTagName, _) ->
    (Nothing, AccState (if l == 0 then i else s) (l + 1) InTagName)
  (InAttr, BGt) ->
    (Just (Prelude.const TTagEnd, 0, 0), AccState i 0 InContent)
  (InAttr, BSlash) ->
    (Just (Prelude.const TSelfClose, 0, 0), AccState i 0 InContent)
  (InAttr, BSpace) ->
    (Nothing, AccState i 0 InAttr)
  (InAttr, _) ->
    (Nothing, AccState (if l == 0 then i else s) (l + 1) InAttr)
  (InClose, BGt) ->
    ( if l == 0 then Nothing else Just (TCloseTag, s, l),
      AccState i 0 InContent
    )
  (InClose, BSpace) ->
    (Nothing, AccState s l InClose)
  (InClose, _) ->
    (Nothing, AccState (if l == 0 then i else s) (l + 1) InClose)
  _ ->
    (Nothing, AccState (if l == 0 then i else s) (l + 1) ctx)

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
      | i >= len = []
      | otherwise =
          let !w = BSU.unsafeIndex bs i
              !bc = classifyByte (accCtx acc) w
              (emit, !acc') = accumStep acc bc i
           in case emit of
                Nothing -> go (i + 1) acc'
                Just (con, s, l) ->
                  let !tok =
                        if l == 0
                          then con BS.empty
                          else con (BSU.unsafeTake l (BSU.unsafeDrop s bs))
                   in tok : go (i + 1) acc'

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
  { oStart :: {-# UNPACK #-} !Int,
    oLen :: {-# UNPACK #-} !Int,
    oCtx :: !MarkupCtx
  }

-- | Step the offset accumulator.
-- Input: (ByteClass, Int, MarkupCtx)  — class, current index, feedback ctx
-- Output: (Maybe emit, new ctx) where emit = (constructor, start, len)
oAccumStep ::
  OAccState ->
  (ByteClass, Int, MarkupCtx) ->
  (Maybe (ByteString -> MarkupToken, Int, Int), OAccState)
oAccumStep (OAccState !s !l !ctx) (bc, !i, _) = case (ctx, bc) of
  (InContent, BLt) ->
    ( if l == 0 then Nothing else Just (TContent, s, l),
      OAccState i 0 InTagName
    )
  (InContent, _) ->
    (Nothing, OAccState (if l == 0 then i else s) (l + 1) InContent)
  (InTagName, BSpace) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l),
      OAccState i 0 InAttr
    )
  (InTagName, BGt) ->
    ( if l == 0 then Nothing else Just (TOpenTag, s, l),
      OAccState i 0 InContent
    )
  (InTagName, BSlash) ->
    if l == 0
      then (Nothing, OAccState i 0 InClose)
      else (Nothing, OAccState s (l + 1) InTagName)
  (InTagName, _) ->
    (Nothing, OAccState (if l == 0 then i else s) (l + 1) InTagName)
  (InAttr, BGt) ->
    (Just (Prelude.const TTagEnd, 0, 0), OAccState i 0 InContent)
  (InAttr, BSlash) ->
    (Just (Prelude.const TSelfClose, 0, 0), OAccState i 0 InContent)
  (InAttr, BSpace) ->
    (Nothing, OAccState i 0 InAttr)
  (InAttr, _) ->
    (Nothing, OAccState (if l == 0 then i else s) (l + 1) InAttr)
  (InClose, BGt) ->
    ( if l == 0 then Nothing else Just (TCloseTag, s, l),
      OAccState i 0 InContent
    )
  (InClose, BSpace) -> (Nothing, OAccState s l InClose)
  (InClose, _) ->
    (Nothing, OAccState (if l == 0 then i else s) (l + 1) InClose)
  _ ->
    (Nothing, OAccState (if l == 0 then i else s) (l + 1) ctx)

data MAccState = MAccState ![Word8] !MarkupCtx

classW :: ByteClass -> Word8
classW (BAlpha w) = w
classW (BQuote c) = fromIntegral (ord c)
classW BSpace = 32
classW BDash = 45
classW BEquals = 61
classW _ = 63

mAccumStep :: MAccState -> (ByteClass, MarkupCtx) -> (Maybe MarkupToken, MAccState)
mAccumStep (MAccState buf ctx) (bc, _) = case (ctx, bc) of
  (InContent, BLt) ->
    ( if Prelude.null buf
        then Nothing
        else Just (TContent (BS.pack (Prelude.reverse buf))),
      MAccState [] InTagName
    )
  (InContent, _) -> (Nothing, MAccState (classW bc : buf) InContent)
  (InTagName, BSpace) ->
    ( if Prelude.null buf
        then Nothing
        else Just (TOpenTag (BS.pack (Prelude.reverse buf))),
      MAccState [] InAttr
    )
  (InTagName, BGt) ->
    ( if Prelude.null buf
        then Nothing
        else Just (TOpenTag (BS.pack (Prelude.reverse buf))),
      MAccState [] InContent
    )
  (InTagName, BSlash) ->
    if Prelude.null buf
      then (Nothing, MAccState [] InClose)
      else (Nothing, MAccState (47 : buf) InTagName)
  (InTagName, _) -> (Nothing, MAccState (classW bc : buf) InTagName)
  (InAttr, BGt) -> (Just TTagEnd, MAccState [] InContent)
  (InAttr, BSlash) -> (Just TSelfClose, MAccState [] InContent)
  (InAttr, BSpace) -> (Nothing, MAccState [] InAttr)
  (InAttr, _) -> (Nothing, MAccState (classW bc : buf) InAttr)
  (InClose, BGt) ->
    ( if Prelude.null buf
        then Nothing
        else Just (TCloseTag (BS.pack (Prelude.reverse buf))),
      MAccState [] InContent
    )
  (InClose, BSpace) -> (Nothing, MAccState buf InClose)
  (InClose, _) -> (Nothing, MAccState (classW bc : buf) InClose)
  _ -> (Nothing, MAccState (classW bc : buf) ctx)

-- ---------------------------------------------------------------------------
-- Traced (->) a (OAccState -> (Maybe token, OAccState))
-- ---------------------------------------------------------------------------
--
-- Output type is State OAccState (Maybe token).
-- OAccState carries MarkupCtx — no feedback wire, no Loop, no knot.
-- runFn gives WI -> OAccState -> (Maybe token, OAccState).
-- Driver seeds with OAccState 0 0 InContent and threads state explicitly.

-- | Stage 1 as a plain function over (WI, OAccState).
-- Classifies the byte using ctx from OAccState, returns updated OAccState.
stage1S :: (WI, OAccState) -> ((ByteClass, Int), OAccState)
stage1S (WI w i, acc) = ((classifyByte (oCtx acc) w, i), acc)

-- | Stage 2 as a plain function over ((ByteClass, Int), OAccState).
stage2S :: ((ByteClass, Int), OAccState) -> (Maybe (ByteString -> MarkupToken, Int, Int), OAccState)
stage2S ((bc, i), acc) = oAccumStep acc (bc, i, oCtx acc)

-- | Markup lexer as Traced (->) with OAccState threaded as output.
-- No Loop — OAccState carries MarkupCtx, threaded by the driver.
-- Compose stage2S stage1S lifts to Traced (->).
markupLexerS :: Traced (->) WI (OAccState -> (Maybe (ByteString -> MarkupToken, Int, Int), OAccState))
markupLexerS = Lift $ \wi acc -> stage2S (stage1S (wi, acc))

-- | Compiled step function.
stepMarkupS :: WI -> OAccState -> (Maybe (ByteString -> MarkupToken, Int, Int), OAccState)
stepMarkupS = run markupLexerS

-- | Initial accumulator state.
initOAccState :: OAccState
initOAccState = OAccState 0 0 InContent

-- | Run via Traced (->) State pipeline.
runMarkupStateBS :: ByteString -> [MarkupToken]
runMarkupStateBS bs
  | BS.null bs = []
  | otherwise =
      let !w0 = BSU.unsafeHead bs
          (mEmit, !s0) = stepMarkupS (WI w0 0) initOAccState
          toks0 = case mEmit of
            Nothing -> []
            Just (con, start, len) -> [mkTok con start len]
       in toks0 ++ go s0 1 (BSU.unsafeTail bs)
  where
    go !acc !i bs'
      | BS.null bs' = []
      | otherwise =
          let !w = BSU.unsafeHead bs'
              (mEmit, !acc') = stepMarkupS (WI w i) acc
           in case mEmit of
                Nothing ->
                  go acc' (i + 1) (BSU.unsafeTail bs')
                Just (con, start, len) ->
                  mkTok con start len : go acc' (i + 1) (BSU.unsafeTail bs')
    mkTok con start len
      | len == 0 = con BS.empty
      | otherwise = con (BSU.unsafeTake len (BSU.unsafeDrop start bs))

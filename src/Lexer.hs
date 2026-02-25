{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- |
-- Module      : Lexer
-- Description : State-machine lexers via Mealy machines
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
  , runMarkupLexerBS
  , runMarkupMealyBS
    -- * Internal machinery (for LexerTraced)
  , WI (..)
  , AccState (..)
  , ByteClass (..)
  , classifyByte
  , accumStep
  ) where

import Prelude hiding (id, (.))
import qualified Prelude

import Data.Function (fix)
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

import qualified Data.Mealy as DM
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
-- Markup lexer as Mealy machine
-- ---------------------------------------------------------------------------

-- | Markup lexer as a Mealy machine.
-- State carries (AccState, Maybe emit) where emit is the slice coordinates.
-- Input is WI (Word8, Int) — byte paired with its index.
-- Zero-copy token emission via unsafeTake/unsafeDrop.
markupLexerMealy :: DM.Mealy WI (Maybe (ByteString -> MarkupToken, Int, Int))
markupLexerMealy = DM.M
  -- inject: initialize with empty accumulator, no emit
  (\(WI _ i) -> (AccState i 0 InContent, Nothing))
  
  -- step: classify byte, apply accumStep to compute new state and emit
  (\(acc, _) (WI w i) ->
    let bc = classifyByte (accCtx acc) w
        (emit, acc') = accumStep acc bc i
    in (acc', emit))
  
  -- extract: return the emit that step just computed
  (\(_, emit) -> emit)

-- | Run markup lexer via Mealy with index threading.
-- Takes WI (Word8, Int) as input.
-- State carries (AccState, emit) where emit is the result of the last step.
runMarkupMealyBS :: ByteString -> [MarkupToken]
runMarkupMealyBS bs = 
  case markupLexerMealy of
    DM.M inject step extract ->
      let go !s !i bs'
            | BS.null bs' = []
            | otherwise =
                let !w = BSU.unsafeHead bs'
                    !s' = step s (WI w i)
                    !mEmit = extract s'
                in case mEmit of
                     Nothing ->
                       go s' (i+1) (BSU.unsafeTail bs')
                     Just (con, start, len) ->
                       let !tok = if len == 0
                                   then con BS.empty
                                   else con (BSU.unsafeTake len (BSU.unsafeDrop start bs))
                       in tok : go s' (i+1) (BSU.unsafeTail bs')
      in if BS.null bs then []
         else let !w0 = BSU.unsafeHead bs
              in go (inject (WI w0 0)) 1 (BSU.unsafeTail bs)

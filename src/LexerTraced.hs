{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- |
-- Module      : LexerTraced
-- Description : Markup lexer via Traced Mealy with composition and feedback
--
-- This module tests the full Traced machinery:
-- - Lift Mealy machines into Traced
-- - Compose them with Traced.Compose
-- - Close feedback loop with Traced.Loop
-- - Interpret back to Mealy with the generic run
--
-- This exercises: Strong (first'), Costrong (unfirst), Compose, Loop

module LexerTraced
  ( runMarkupLexerTracedBS
  ) where

import Prelude hiding (id, (.))
import qualified Prelude

import Data.Word (Word8)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU

import qualified Data.Mealy as DM
import Traced (Traced (..), run)
import Control.Category ((.))
import Lexer (MarkupCtx (..), MarkupToken (..), WI (..), AccState (..), 
              classifyByte, accumStep, ByteClass (..))

-- ---------------------------------------------------------------------------
-- Stage 1: Classify byte, thread index and context through
-- ---------------------------------------------------------------------------

-- | Stage 1 Mealy: (WI, MarkupCtx) -> ((ByteClass, Int), MarkupCtx)
-- Input:  WI (byte + index) paired with feedback context
-- Output: ByteClass + index, paired with feedback context
-- State:  (WI, MarkupCtx) — just the input
stage1Mealy :: DM.Mealy (WI, MarkupCtx) ((ByteClass, Int), MarkupCtx)
stage1Mealy = DM.M
  -- inject: store input as state
  (\input -> input)
  -- step: update state with new input
  (\_ input -> input)
  -- extract: classify and return the result
  (\(WI w i, ctx) -> ((classifyByte ctx w, i), ctx))

-- ---------------------------------------------------------------------------
-- Stage 2: Accumulate offsets, emit tokens
-- ---------------------------------------------------------------------------

-- | Stage 2 Mealy: ((ByteClass, Int), MarkupCtx) -> (Maybe emit, MarkupCtx)
-- Input:  ByteClass + index, paired with feedback context
-- Output: Maybe token emit, paired with feedback context
-- State:  (Maybe emit, AccState) — current emit and accumulator
stage2Mealy :: DM.Mealy ((ByteClass, Int), MarkupCtx)
                        (Maybe (ByteString -> MarkupToken, Int, Int), MarkupCtx)
stage2Mealy = DM.M
  -- inject: initialize with empty accumulator (lazy pattern)
  (\input -> case input of
      ((_, i), ctx) -> (Nothing, AccState i 0 ctx))
  -- step: run accumStep, store result in state
  (\state input -> case input of
      ((bc, i), newCtx) -> 
        case state of
          (_, acc) -> 
            let acc' = acc { accCtx = newCtx }
                (emit, acc'') = accumStep acc' bc i
            in (emit, acc''))
  -- extract: return the stored emit and context
  (\state -> case state of
      (emit, acc) -> (emit, accCtx acc))

-- ---------------------------------------------------------------------------
-- Full pipeline via Traced composition and Loop
-- ---------------------------------------------------------------------------

-- | Combined pipeline: stage1 and stage2 as a single Mealy
-- Input: (WI, MarkupCtx)
-- Output: (Maybe emit, MarkupCtx)
pipelineMealy :: DM.Mealy (WI, MarkupCtx) (Maybe (ByteString -> MarkupToken, Int, Int), MarkupCtx)
pipelineMealy = stage2Mealy . stage1Mealy

-- | Lift the combined pipeline into Traced and close the loop
-- This exercises: Lift, Loop, Costrong (via unfirst)
-- NOTE: This currently deadlocks due to strictness in Mealy composition + unfirst lazy knot
-- See: ~/markdown-general/yin/traced-machinery-test-report.md
markupLexerTracedPipeline :: Traced DM.Mealy WI (Maybe (ByteString -> MarkupToken, Int, Int))
markupLexerTracedPipeline = Loop (Lift pipelineMealy)

-- | Interpret the Traced pipeline back to a Mealy machine
-- This uses the generic run with Mealy's Costrong instance
-- KNOWN ISSUE: This deadlocks on actual execution
markupLexerFinal :: DM.Mealy WI (Maybe (ByteString -> MarkupToken, Int, Int))
markupLexerFinal = run markupLexerTracedPipeline

-- ---------------------------------------------------------------------------
-- Runner: Direct ByteString driver
-- ---------------------------------------------------------------------------

-- | Run markup lexer via Traced machinery over a ByteString
runMarkupLexerTracedBS :: ByteString -> [MarkupToken]
runMarkupLexerTracedBS bs =
  case markupLexerFinal of
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

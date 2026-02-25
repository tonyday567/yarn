#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.ByteString as BS
import LexerTraced (stage1Mealy, stage2Mealy)
import qualified Data.Mealy as DM
import Lexer (WI(..), MarkupCtx(..), classifyByte, accumStep, ByteClass(..))
import Data.Word (Word8)

main :: IO ()
main = do
  -- Test stage1 directly
  putStrLn "Testing stage1Mealy..."
  case stage1Mealy of
    DM.M inj1 step1 ext1 -> do
      let state1 = inj1 (WI 60 0, InContent)  -- '<' at index 0
      let result1 = ext1 state1
      putStrLn $ "Stage1 result: " ++ show result1
      
  -- Test stage2 directly
  putStrLn "Testing stage2Mealy..."
  case stage2Mealy of
    DM.M inj2 step2 ext2 -> do
      let state2_init = inj2 ((BLt, 0), InContent)
      let result2_init = ext2 state2_init
      putStrLn $ "Stage2 init result: " ++ show result2_init
      
  putStrLn "Done!"

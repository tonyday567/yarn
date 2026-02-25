#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import Traced (Traced(..), run)
import Lexer (WI(..), MarkupCtx(..), AccState(..), classifyByte, accumStep, ByteClass(..))
import Prelude hiding ((.), id)
import Control.Category ((.), id)
import Data.Word (Word8)

-- Exact stage1 from LexerTraced
stage1 :: DM.Mealy (WI, MarkupCtx) ((ByteClass, Int), MarkupCtx)
stage1 = DM.M
  (\input -> input)
  (\_ input -> input)
  (\(WI w i, ctx) -> ((classifyByte ctx w, i), ctx))

-- Exact stage2 from LexerTraced (using dummy emit type)
stage2 :: DM.Mealy ((ByteClass, Int), MarkupCtx)
                    (Maybe (), MarkupCtx)
stage2 = DM.M
  (\input -> case input of
      ((_, i), ctx) -> (Nothing, AccState i 0 ctx))
  (\state input -> case input of
      ((bc, i), newCtx) -> 
        case state of
          (_, acc) -> 
            let acc' = acc { accCtx = newCtx }
                (emit, acc'') = accumStep acc' bc i
            in (emit, acc''))
  (\state -> case state of
      (emit, acc) -> case emit of
                       Nothing -> (Nothing, accCtx acc)
                       Just _ -> (Nothing, accCtx acc))

main :: IO ()
main = do
  putStrLn "Test 1: Stage1 alone"
  case stage1 of
    DM.M inj step ext -> do
      let s0 = inj (WI 60 0, InContent)
      let result = ext s0
      putStrLn $ "Stage1 result: " ++ show result
  
  putStrLn "\nTest 2: Composed stage1 . stage2"
  let composed = stage2 . stage1
  case composed of
    DM.M inj step ext -> do
      let s0 = inj (WI 60 0, InContent)
      let result = ext s0
      putStrLn $ "Composed result: " ++ show result
  
  putStrLn "\nTest 3: Composed wrapped in Loop/Traced/run"
  let tracedComposed = Lift composed
  putStrLn "Lift created, making Loop..."
  let loopComposed = Loop tracedComposed
  putStrLn "Loop created, calling run..."
  let result = run loopComposed
  putStrLn "run returned successfully!"
  case result of
    DM.M inj step ext -> do
      putStrLn "Injecting WI 60 0..."
      let s0 = inj (WI 60 0)
      putStrLn "Got state!"
      let out = ext s0
      putStrLn $ "Result: " ++ show out

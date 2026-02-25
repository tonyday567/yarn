#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import Data.Mealy (Mealy(..))
import Traced (Traced(..), run)
import Prelude hiding ((.), id)
import Control.Category ((.), id)

-- For Loop, we need Mealy (a, c) (b, c)
-- Let's use: a=Int, c=String, b=Int
-- Stage 1: Extract a and pass c through
stage1 :: Mealy (Int, String) (Int, String)
stage1 = DM.M
  id
  (\_ input -> input)
  id

-- Stage 2: Transform output and pass c through
stage2 :: Mealy (Int, String) (Int, String)
stage2 = DM.M
  id
  (\_ input -> input)
  (\(a, c) -> (a + 1, c))  -- increment the value

-- Composed: stage2 . stage1
composed :: Mealy (Int, String) (Int, String)
composed = stage2 . stage1

main :: IO ()
main = do
  putStrLn "Test 1: Composing two simple Mealy machines (direct)"
  case composed of
    DM.M inj step ext -> do
      putStrLn "Injecting (42, 'hello')..."
      let s0 = inj (42, "hello")
      putStrLn "Got state, extracting..."
      let result = ext s0
      putStrLn $ "Result: " ++ show result
      
      putStrLn "\nTesting step..."
      let s1 = step s0 (100, "world")
      let result1 = ext s1
      putStrLn $ "After step: " ++ show result1
  
  putStrLn "\n\nTest 2: Wrapped in Loop/Traced/run"
  let tracedComposed = Lift composed :: Traced Mealy (Int, String) (Int, String)
  putStrLn "Created Traced composition, about to call run on Loop..."
  let loopComposed = Loop tracedComposed
  putStrLn "Loop constructed, calling run..."
  let result = run loopComposed
  putStrLn "run returned successfully, extracting Mealy..."
  case result of
    DM.M inj step ext -> do
      putStrLn "Injecting 42..."
      let s0 = inj 42
      putStrLn "Got state, extracting..."
      let out = ext s0
      putStrLn $ "Result: " ++ show out

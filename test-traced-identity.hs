#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import Traced (Traced(..), run)

-- Identity Mealy: passes input through unchanged
idMealy :: DM.Mealy Int Int
idMealy = DM.M id (\s _ -> s) id

-- Lift into Traced
idTraced :: Traced DM.Mealy Int Int
idTraced = Lift idMealy

-- Run the Lifted Mealy back through generic run
idInterpreted :: DM.Mealy Int Int
idInterpreted = run idTraced

main :: IO ()
main = do
  putStrLn "Test 1: Direct identity Mealy"
  case idMealy of
    DM.M inj step ext -> do
      let s0 = inj 42
      let result = ext s0
      putStrLn $ "Identity on 42: " ++ show result
  
  putStrLn "\nTest 2: Via Traced.Lift + generic run"
  case idInterpreted of
    DM.M inj step ext -> do
      let s0 = inj 42
      let result = ext s0
      putStrLn $ "Lifted identity on 42: " ++ show result
  
  putStrLn "\nTest 3: Loop with identity Mealy"
  let feedbackMealy :: DM.Mealy (Int, String) (Int, String)
      feedbackMealy = DM.M id (\s _ -> s) id
  let loopIdTraced :: Traced DM.Mealy Int Int
      loopIdTraced = Loop (Lift feedbackMealy)
  putStrLn "Created Loop Traced, calling run..."
  let loopIdInterpreted = run loopIdTraced
  putStrLn "run returned, extracting Mealy..."
  case loopIdInterpreted of
    DM.M inj step ext -> do
      putStrLn "Attempting to inject 42 into Loop..."
      let s0 = inj 42
      putStrLn "Got state, extracting..."
      let result = ext s0
      putStrLn $ "Loop identity on 42: " ++ show result
  
  putStrLn "\nTest 4: Loop with stateful Mealy (accumulator)"
  -- A Mealy that accumulates the first component
  let accumMealy :: DM.Mealy (Int, Int) (Int, Int)
      accumMealy = DM.M 
        (\(a, c) -> a)  -- inject: take first component
        (\s (a, c) -> s + a)  -- step: accumulate
        (\s -> (s, s))  -- extract: return both as pair (threading feedback)
  let loopAccumTraced = Loop (Lift accumMealy)
  putStrLn "Created Loop with accumulator, calling run..."
  let loopAccumInterpreted = run loopAccumTraced
  putStrLn "run returned, testing..."
  case loopAccumInterpreted of
    DM.M inj step ext -> do
      putStrLn "Injecting 10..."
      let s0 = inj 10
      putStrLn "Got state, extracting..."
      let result = ext s0
      putStrLn $ "Accumulator result: " ++ show result

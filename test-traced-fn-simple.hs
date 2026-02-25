#!/usr/bin/env runhaskell

import Traced (Traced(..), runFn)

-- Test 1: Identity
idFn :: (Int, String) -> (Int, String)
idFn = id

idTraced :: Traced (->) (Int, String) (Int, String)
idTraced = Lift idFn

idLooped :: Traced (->) Int Int
idLooped = Loop idTraced

-- Test 2: Fixed point function
-- Takes (Int, Int) and outputs (Int, Int)
-- Needs a fixed point: (b, c) = fixedPt (a, c)
-- Simple: output is the input, feedback is constant
fixedPtFn :: (Int, Int) -> (Int, Int)
fixedPtFn (a, c) = (a, 0)  -- output a, pass 0 as feedback

fixedPtTraced :: Traced (->) (Int, Int) (Int, Int)
fixedPtTraced = Lift fixedPtFn

fixedPtLooped :: Traced (->) Int Int
fixedPtLooped = Loop fixedPtTraced

main :: IO ()
main = do
  putStrLn "Test 1: Simple Loop in Traced (->) with identity"
  let fn1 = runFn idLooped
  putStrLn "runFn returned"
  let result1 = fn1 42
  putStrLn $ "Result: " ++ show result1
  
  putStrLn "\nTest 2: Loop with fixed point"
  let fn2 = runFn fixedPtLooped
  putStrLn "runFn returned for fixed point"
  let result2 = fn2 10
  putStrLn $ "Result: " ++ show result2

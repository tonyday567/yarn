#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import Traced (Traced(..), run)
import Prelude hiding ((.), id)
import Control.Category ((.), id)

-- Simple pipeline that threads feedback
pipelineFn :: (Int, String) -> (Int, String)
pipelineFn (a, c) = (a + 1, "feedback")

pipelineTraced :: Traced DM.Mealy (Int, String) (Int, String)
pipelineTraced = Lift (DM.M id (\s _ -> s) pipelineFn)

-- Close the loop
loopPipeline = Loop pipelineTraced

-- Interpret to Mealy
finalMealy = run loopPipeline

main :: IO ()
main = do
  putStrLn "Test: Repeatedly calling extract on looped Mealy"
  
  case finalMealy of
    DM.M inject step extract -> do
      putStrLn "Injecting 0..."
      let s0 = inject 0
      putStrLn "Got state"
      
      putStrLn "Calling step and extract in a loop..."
      let s1 = step s0 1
      putStrLn $ "Step 1: " ++ show (extract s1)
      
      let s2 = step s1 2
      putStrLn $ "Step 2: " ++ show (extract s2)
      
      let s3 = step s2 3
      putStrLn $ "Step 3: " ++ show (extract s3)

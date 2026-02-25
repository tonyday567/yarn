#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import Traced (Traced(..), run)
import Lexer (AccState(..), MarkupCtx(..), accumStep, ByteClass(..))
import Prelude hiding ((.), id)
import Control.Category ((.), id)

-- Stage that uses AccState
stageWithAccState :: DM.Mealy (ByteClass, MarkupCtx) (Maybe (), MarkupCtx)
stageWithAccState = DM.M
  (\(bc, ctx) -> AccState 0 0 ctx)  -- inject: create AccState
  (\acc (bc, ctx) ->
    let (_, acc') = accumStep acc bc 0  -- step
    in acc')
  (\acc -> (Nothing, accCtx acc))  -- extract: return context

main :: IO ()
main = do
  putStrLn "Test: Loop with AccState-using Mealy"
  let tracedStage = Lift stageWithAccState
  putStrLn "Created Lift, calling run on Loop..."
  let loopStage = Loop tracedStage
  putStrLn "Loop created, about to call run..."
  let result = run loopStage
  putStrLn "run returned!"
  case result of
    DM.M inj step ext -> do
      putStrLn "Injecting BLt..."
      let s0 = inj BLt
      putStrLn "Got state!"
      let out = ext s0
      putStrLn $ "Result: " ++ show out

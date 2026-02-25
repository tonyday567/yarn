#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Mealy as DM
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU
import Traced (Traced(..), run)
import Lexer (WI(..), MarkupCtx(..), AccState(..), classifyByte, accumStep, ByteClass(..))
import Prelude hiding ((.), id)
import Control.Category ((.), id)

main :: IO ()
main = do
  putStrLn "Test: Loop + step/extract with actual pipelineMealy"
  
  -- Rebuild stages inline
  let stage1 :: DM.Mealy (WI, MarkupCtx) ((ByteClass, Int), MarkupCtx)
      stage1 = DM.M
        (\input -> input)
        (\_ input -> input)
        (\(WI w i, ctx) -> ((classifyByte ctx w, i), ctx))
  
  let stage2 :: DM.Mealy ((ByteClass, Int), MarkupCtx) (Maybe (String, Int, Int), MarkupCtx)
      stage2 = DM.M
        (\input -> case input of ((_, i), ctx) -> (Nothing, AccState i 0 ctx))
        (\state input -> case input of
          ((bc, i), newCtx) -> case state of
            (_, acc) -> 
              let acc' = acc { accCtx = newCtx }
                  (emit, acc'') = accumStep acc' bc i
              in case emit of
                   Nothing -> (Nothing, acc'')
                   Just (_, s, l) -> (Just ("token", s, l), acc''))
        (\state -> case state of
          (emit, acc) -> (emit, accCtx acc))
  
  let pipelineMealy = stage2 . stage1
  let loopPipeline = Loop (Lift pipelineMealy)
  putStrLn "Loop created, calling run..."
  
  let finalMealy = run loopPipeline
  putStrLn "run returned!"
  
  case finalMealy of
    DM.M inject step extract -> do
      putStrLn "Injecting WI 60 0..."
      let s0 = inject (WI 60 0)
      putStrLn "Got state"
      
      putStrLn "Calling extract..."
      let result0 = extract s0
      putStrLn $ "Extract 1: " ++ show result0
      
      putStrLn "Running with actual ByteString iteration..."
      let bs = "<test>"
          go !s !i !bs'
            | BS.null bs' = putStrLn "ByteString loop done"
            | otherwise =
                let !w = BSU.unsafeHead bs'
                    !s' = step s (WI w i)
                    !mEmit = extract s'
                in do
                  putStrLn $ "Byte " ++ show i ++ ": " ++ show mEmit
                  go s' (i+1) (BSU.unsafeTail bs')
      
      go s0 1 (BSU.unsafeTail bs)

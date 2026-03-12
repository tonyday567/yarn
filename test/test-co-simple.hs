-- Test: Co coroutine protocol
-- Goal: Simple generator/consumer handshake

{-# LANGUAGE RankNTypes #-}

import Control.Monad.Cont
import Hyp

-- Simple test: a generator that yields integers
-- and a consumer that collects them

-- Generator that yields 1, 2, 3, then returns ()
gen :: Co () Int Int m ()
gen = undefined

-- Consumer that reads 3 integers and sums them
consumer :: Co Int Int Int m Int
consumer = undefined

-- Test: run a handshake
-- Should send 1, get 1 back
-- Should send 2, get 2 back
-- Should send 3, get 3 back
-- Then generator returns

main :: IO ()
main = do
  putStrLn "Testing Co coroutine protocol"
  -- result <- runContT (send' consumer 0) pure
  -- print result
  putStrLn "TODO: implement Co examples"

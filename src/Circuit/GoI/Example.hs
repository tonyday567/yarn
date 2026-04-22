{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.GoI.Example where

import Control.Arrow (Kleisli (..), runKleisli)
import Circuit
import Circuit.GoI ()
import Prelude hiding (id, (.))

-- | A simple feedback loop using the delimited-continuation Trace instance.
--
-- This implements a countdown printer that would normally be written recursively:
--
--     countdown n = if n <= 0 then pure () else print n *> countdown (n-1)
--
-- With the standard (->) Trace instance that would blow the stack for large n.
-- With the GoI delimited-continuation Trace it uses constant stack space —
-- exactly the powerful combination you were looking for.

step :: Kleisli IO (Either Int Int) (Either Int ())
step = Kleisli \case
  Left n  -> handle n
  Right n -> handle n   -- first invocation starts with Right initial value
  where
    handle n
      | n <= 0    = pure (Right ())
      | otherwise = do
          putStrLn $ "tick " <> show n
          pure (Left (n - 1))

-- | The full Circuit that exposes the countdown as a normal Kleisli arrow.
countdownCircuit :: Circuit (Kleisli IO) Either Int ()
countdownCircuit = Loop step

-- | Run it.  The Loop is turned into an efficient IO action by the GoI Trace.
countdown :: Int -> IO ()
countdown n = runKleisli (run countdownCircuit) n

-- | Demo
main :: IO ()
main = do
  putStrLn "=== Delimited-continuation Circuit countdown ==="
  countdown 10
  putStrLn "=== Done (no stack overflow even for huge n) ==="

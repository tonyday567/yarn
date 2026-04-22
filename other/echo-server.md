# Echo Server

Iconic long-running echo server / REPL using a single Loop.

Demonstrates:
- Exit path (Right) for clean shutdown
- Constant stack usage via delimited continuations
- Simple user-facing protocol ("quit" to exit)

## Implementation

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Examples.EchoServer where

import Control.Arrow (Kleisli (..), runKleisli)
import Circuit
import Circuit.GoI
import Prelude hiding (id, (.))

-- | Iconic long-running echo server / REPL using a single Loop.
--   Demonstrates:
--   - Exit path (Right) for clean shutdown
--   - Constant stack usage via delimited continuations
--   - Simple user-facing protocol ("quit" to exit)

echoStep :: Kleisli IO (Either String String) (Either String ())
echoStep = Kleisli \case
  Left  line -> handle line
  Right line -> handle line   -- initial call starts with Right
  where
    handle line
      | line `elem` ["quit", "exit", ":q"] = pure (Right ())
      | otherwise = do
          putStrLn $ "echo: " ++ line
          pure (Left "next>")   -- feedback token asks for next line

echoCircuit :: Circuit (Kleisli IO) Either String ()
echoCircuit = loopIO echoStep'
  where
    echoStep' line
      | line `elem` ["quit", "exit", ":q"] = pure (Right ())
      | otherwise = do
          putStrLn $ "echo: " ++ line
          pure (Left "next>")

runEcho :: IO ()
runEcho = do
  putStrLn "=== Echo Server (type lines, 'quit' to exit) ==="
  runKleisli (run echoCircuit) "hello"   -- initial prompt
```

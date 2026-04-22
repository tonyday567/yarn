# Resource File

Safe file resource handling with explicit acquire-use-release via Loop exit path.

The "Right" exit token is the single place where release happens. This pattern guarantees resource cleanup without try-finally boilerplate.

## Implementation

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Examples.ResourceFile where

import Control.Arrow (Kleisli (..), runKleisli)
import Circuit
import Circuit.GoI ()
import System.IO
import Prelude hiding (id, (.))

-- | Safe file resource handling with explicit acquire-use-release via Loop exit path.
--   The "Right ()" exit token is the single place where release happens.

fileResource :: FilePath -> Circuit (Kleisli IO) Either () String
fileResource path = loopIO \case
  () -> do                       -- acquire
    h <- openFile path ReadMode
    pure (Left h)
  h -> do                        -- use + decide to continue or release
    eof <- hIsEOF h
    if eof
      then do
        hClose h
        pure (Right "File read complete")
      else do
        line <- hGetLine h
        putStrLn line
        pure (Left h)            -- continue with same handle

demoResource :: IO ()
demoResource = do
  putStrLn "=== ResourceFile demo (reads itself) ==="
  runKleisli (run (fileResource "Circuit/Examples/ResourceFile.hs")) ()
```

## Pattern

The feedback channel carries the open Handle. When we return `Right`, the loop exits and the handle is guaranteed to be closed in that return statement. This is a natural way to ensure resource cleanup at a specific point.

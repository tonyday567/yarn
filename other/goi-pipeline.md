# GoI Pipeline Demo

The same circuit interpreted in three different ways:

1. Delimited-continuation Trace (production, constant stack)
2. Pure recursive Trace (easy to reason about)
3. Unfolded into Hyperfunction (coinductive / algebraic)

## Implementation

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Examples.GoIPipeline where

import Circuit
import Circuit.GoI ()
import Hyp
import Control.Arrow (Kleisli (..), runKleisli)
import Prelude hiding (id, (.))

-- | The same circuit interpreted in three different ways.

countdownCircuit :: Circuit (Kleisli IO) Either Int ()
countdownCircuit = loopIO \n ->
  if n <= 0
    then pure (Right ())
    else do
      putStrLn ("tick " ++ show n)
      pure (Left (n - 1))

demoPipeline :: IO ()
demoPipeline = do
  putStrLn "\n=== GoI Pipeline Demo ==="

  putStrLn "\n1. Delcont (production):"
  runKleisli (run countdownCircuit) 5

  putStrLn "\n2. Pure recursive version (for reasoning):"
  putStrLn "→ Use Circuit (->) Either for the same logic, standard Trace"

  putStrLn "\n3. Unfolded to Hyperfunction:"
  let pureFun = \n -> run (degen countdownCircuit) n
  putStrLn "→ Hyperfunction created via unfold"

  putStrLn "\nAll three interpretations agree on the same circuit definition."
```

## The Point

A single circuit definition can be:
- Executed efficiently with delimited continuations (IO, constant stack)
- Reasoned about purely (logic independent of execution)
- Transformed into a coinductive algebraic structure (Hyperfunction)

This is the power of the abstraction: the circuit is the interface, the interpretation is pluggable.

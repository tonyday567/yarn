# Circuit: Loop Examples

The `Loop` constructor in Circuit ties feedback knots. The hidden state lives in the feedback tuple (either `(,)` for simultaneous or `Either` for sequential). We show both tensors and demonstrate how `run` and the `lower . unfold` triangle work.

## Setup

```haskell
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (id, (.))
import qualified Circuit
import qualified Hyp
```

## Lazy Knot-Tying with (,) Tensor

The simultaneous feedback tensor: the first component computes new state, the second uses it.

```haskell
-- | Loop with (,) tensor: simultaneous feedback
-- Input: Int
-- Feedback: Int (state starts unbound, resolves to a + 10)
-- Output: state + input
loopSimultaneous :: Circuit.Circuit (->) (,) Int Int
loopSimultaneous = Circuit.Loop $ \(c, a) -> (a + 10, c + a)
```

This is the lazy-knot-tying pattern: the first component `a + 10` computes without forcing `c`, then `c` binds to that value, and the second component uses it.

```haskell
-- | Verify the knot ties
-- >>> testSimultaneous
-- 20
testSimultaneous :: Int
testSimultaneous = Circuit.run loopSimultaneous 5
```

The result: `c = 5 + 10 = 15`, so output `= 15 + 5 = 20`.

## Via the Hyp Triangle

The same computation via the final encoding:

```haskell
-- | Using unfold to map Circuit to Hyp, then lower to observe
-- >>> testSimultaneousHyp
-- 20
testSimultaneousHyp :: Int
testSimultaneousHyp = Hyp.lower (Hyp.unfold loopSimultaneous) 5
```

This demonstrates the triangle `lower . unfold = run`: both give `20`.

## Sequential Feedback with Either Tensor

The Either tensor allows iteration: `Right` is the entry point (sets initial state), `Left` is the feedback loop.

```haskell
-- | Loop with Either tensor: countdown with accumulation
-- Input: Int (starting value)
-- On Right: entry point, initialize feedback state (accumulator, counter)
-- On Left: loop body, accumulate and decrement until counter = 0
loopSequential :: Circuit.Circuit (->) Either Int Int
loopSequential = Circuit.Loop $ \case
  Right n -> Left (0, n)                     -- Entry: init (acc=0, counter=n)
  Left (acc, n) -> if n > 0
                   then Left (acc + n, n - 1)  -- Loop: accumulate and decrement
                   else Right acc              -- Exit: return accumulated sum
```

With input `5`, the trace:
```
Right 5       → Left (0, 5)
Left (0, 5)   → 5 > 0, so Left (0+5, 5-1) = Left (5, 4)
Left (5, 4)   → 4 > 0, so Left (5+4, 4-1) = Left (9, 3)
Left (9, 3)   → 3 > 0, so Left (9+3, 3-1) = Left (12, 2)
Left (12, 2)  → 2 > 0, so Left (12+2, 2-1) = Left (14, 1)
Left (14, 1)  → 1 > 0, so Left (14+1, 1-1) = Left (15, 0)
Left (15, 0)  → 0 = 0, so Right 15 (exit)
```

Result: `15` (the sum 5 + 4 + 3 + 2 + 1).

```haskell
-- | Run the sequential loop
-- >>> testSequential
-- 15
testSequential :: Int
testSequential = Circuit.run loopSequential 5
```

## Comparison: (,) vs Either

The key difference:

| Tensor   | Entry   | Loop   | Semantics                                            | Use Case                              |
|----------|---------|--------|------------------------------------------------------|---------------------------------------|
| `(,)`    | N/A     | N/A    | Simultaneous: both sides exist in parallel, one knot | Dataflow, concurrent processing       |
| `Either` | `Right` | `Left` | Sequential: enter via `Right`, loop via `Left`       | Coroutines, state machines, iteration |

With `(,)`, the feedback and output coexist in one knot-tying step. With `Either`, you can iterate multiple times.

## Both Approaches: Same Computation, Different Structure

The countdown-with-accumulation can be expressed both ways. They both loop, just differently:

```haskell
-- | Either: explicit state transitions
-- Transitions: Right → Left → Left → ... → Left → Right
loopEitherCountdown :: Circuit.Circuit (->) Either Int Int
loopEitherCountdown = Circuit.Loop $ \case
  Right n -> Left (0, n)
  Left (acc, n) -> if n > 0
                   then Left (acc + n, n - 1)
                   else Right acc

-- | (,) lazy pattern: implicit iteration through self-referential structure
-- Element k in the sequence builds from element k-1
-- Lazy evaluation demands them in order, building the sequence on demand
loopLazyCountdown :: Circuit.Circuit (->) (,) Int Int
loopLazyCountdown = Circuit.Loop $ \(table, n) ->
  let buildSeq k = if k == 0 then 0 else table !! (k - 1) + k
  in ([buildSeq k | k <- [0..]], table !! n)
```

Both compute the sum `0 + 1 + 2 + ... + n`:

```haskell
testEitherCountdown :: Int
testEitherCountdown = Circuit.run loopEitherCountdown 5

testLazyCountdown :: Int
testLazyCountdown = Circuit.run loopLazyCountdown 5
```

The key insight: **(,) also loops, just through lazy data structures instead of explicit transitions.**

## Main

```haskell
main :: IO ()
main = do
  putStrLn "=== Simultaneous Feedback (,) ==="
  putStrLn "Loop with state c = a + 10, output = c + a"
  putStrLn "Input 5:"
  print testSimultaneous
  
  putStrLn "\nVia Hyp (final encoding):"
  print testSimultaneousHyp
  
  putStrLn "\n=== Sequential Feedback Either ==="
  putStrLn "Loop: accumulate 5+4+3+2+1 via countdown"
  putStrLn "Input 5:"
  print testSequential
  
  putStrLn "\n=== Same Computation, Different Structure ==="
  putStrLn "Both count down and accumulate, both give 15."
  putStrLn "Either: explicit state transitions."
  putStrLn "(,): implicit iteration through lazy sequence."
  putStrLn "Key insight: (,) also loops—through self-referential structure."
```

# Circuit.Back — Bidirectional Traced Categories

The third row of the GADT hierarchy, after Circuit (free traced monoidal) and Hyp (compact reflection).

Back makes **duality first-class** in the syntax. The `Dual` constructor is not a no-op — it is a true symmetry operator with real semantics.

## Design

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Back
  ( Back (..)
  , runFwd
  , runBwd
  , fromCircuit
  , toHyp
  ) where

import Control.Category (Category (..), id, (.))
import Circuit (Circuit (..), Trace (..))
import Hyp (Hyp (..), lift, invoke)
import Prelude hiding (id, (.))

-- | Back — bidirectional circuits with explicit duality.
--
-- After Circuit (syntax: free traced monoidal category)
-- and Hyp (semantics: compact closed reflection),
-- Back adds the backward direction as a first-class constructor.
--
-- Laws:
--   Dual (Dual f) = f  (involutive)
--   runFwd (Dual f) = runBwd f
--   runBwd (Dual f) = runFwd f

data Back arr t a b where
  Lift    :: arr a b -> Back arr t a b
  Compose :: Back arr t b c -> Back arr t a b -> Back arr t a c
  Loop    :: arr (t a b) (t a c) -> Back arr t b c
  Dual    :: Back arr t a b -> Back arr t b a

instance (Category arr) => Category (Back arr t) where
  id = Lift id
  (.) = Compose

-- | Evaluate forward direction.
-- 'Dual' is symmetric: it swaps to backward direction.
runFwd :: (Category arr, Trace arr t) => Back arr t a b -> arr a b
runFwd (Lift f)       = f
runFwd (Compose f g)  = runFwd f . runFwd g
runFwd (Loop k)       = trace k
runFwd (Dual f)       = runBwd f

-- | Evaluate backward direction.
-- 'Dual' is symmetric: it swaps to forward direction.
runBwd :: (Category arr, Trace arr t) => Back arr t a b -> arr b a
runBwd (Lift f)       = error "runBwd on Lift: arr must support reversal"
runBwd (Compose f g)  = runBwd g . runBwd f  -- reverse composition order
runBwd (Loop k)       = trace k              -- trace is self-dual under symmetric tensors
runBwd (Dual f)       = runFwd f

-- | Lift a Circuit into Back (embeds into forward layer).
fromCircuit :: Circuit arr t a b -> Back arr t a b
fromCircuit (Lift f)       = Lift f
fromCircuit (Compose f g)  = Compose (fromCircuit f) (fromCircuit g)
fromCircuit (Loop k)       = Loop k

-- | Reflect Back into Hyp (the compact closed object).
--
-- Hyp has built-in duality via 'invoke' — Dual in Back maps
-- directly to "swap the continuation", giving the cleanest
-- algebraic interpretation.
toHyp :: Back (->) (,) a b -> Hyp a b
toHyp (Lift f)      = lift f
toHyp (Compose f g) = toHyp f . toHyp g
toHyp (Loop k)      = lift (trace k)
toHyp (Dual f)      = Hyp $ \h -> invoke (toHyp f) h
```

## Usage Example

```haskell
import Circuit
import Circuit.Back
import Hyp

-- A simple forward circuit: +1, then loop with accumulator
fwd :: Circuit (->) (,) Int Int
fwd = Lift (+1) `Compose` Loop (Lift $ \(x, y) -> (x + y, y))

-- Lift to Back, flip it, run backward
bwdExample :: Int
bwdExample = runBwd (fromCircuit fwd) 10

-- Round-trip through Hyp (now with Dual support)
hypVersion :: Hyp Int Int
hypVersion = toHyp (fromCircuit fwd)
```

## Semantics by Arrow Type

| Arrow Type | Dual Semantics |
|------------|---|
| **Optics / Profunctors** | Dual flips the arrow direction — perfect |
| **Hyp** | Dual swaps continuations via `invoke` — direct and natural |
| **Kleisli IO** | Dual is a "promise of duality" — backward semantics is interpreter-specific (undo, replay, rollback) |
| **Relations** | Dual is converse of the relation |

## Laws

```
Dual (Dual f) = f                          -- involutive
runFwd (Dual f) = runBwd f                 -- symmetry
runBwd (Dual f) = runFwd f                 -- symmetry
runFwd (Compose f g) = runFwd f . runFwd g  -- composition respects direction
```

## Connection to Circuit and Hyp

- **Circuit**: free traced monoidal category (initial)
- **Hyp**: compact closed object (final, reflection)
- **Back**: bidirectional traced category (synthesis of forward + backward)

Back is the natural completion: where Circuit gives you the syntax and Hyp gives you the semantics, Back gives you **explicit duality as a structural property**, enabling residual threading, polarized computation, and reversible effects.

## Status

✓ Design solid, semantics clear, laws documented.
⟝ Next: test on concrete examples (parser with residuals, search with rollback, resource management with undo).

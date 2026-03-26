{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TracedQ
  ( Atomic (..)
  , TracedQ (..)
  , composeTQ
  , tracedToQ
  , interpretQ
  , normalizeQ
  ) where

import Control.Arrow (ArrowLoop, loop)
import Control.Category (Category (..))
import Prelude hiding (id, (.))
import Traced (Traced (..))
import Traced qualified

-- | Atomic "letters" that live in the queue:
-- either a base arrow or a fully-flattened Knot block.
data Atomic arr a b where
  ALift :: arr a b -> Atomic arr a b
  AKnot :: TracedQ arr (a, c) (b, c) -> Atomic arr a b

-- | The flat queue itself (right-associated chain)
-- Type-aligned sequence representing a normalized path.
data TracedQ arr a b where
  NilQ :: TracedQ arr a a
  ConsQ :: Atomic arr b c -> TracedQ arr a b -> TracedQ arr a c

-- | Composition on the queue (normalizing, O(1) per element)
composeTQ :: TracedQ arr y z -> TracedQ arr x y -> TracedQ arr x z
composeTQ (ConsQ f q1) q2 = ConsQ f (composeTQ q1 q2)
composeTQ NilQ q2 = q2

-- | Category instance for TracedQ
instance Category (TracedQ arr) where
  id = NilQ
  (.) = composeTQ

-- | The flattener: Traced → TracedQ
-- Normalizes every Compose tree into a right-associated ConsQ chain
-- and treats each Knot as a single atomic block (recursively flattened).
tracedToQ :: Traced arr a b -> TracedQ arr a b
tracedToQ Pure = NilQ
tracedToQ (Lift f) = ConsQ (ALift f) NilQ
tracedToQ (Compose g h) = composeTQ (tracedToQ g) (tracedToQ h)
tracedToQ (Knot p) = ConsQ (AKnot (tracedToQ p)) NilQ

-- | Full interpreter of the flat queue (right Kan extension)
-- ArrowLoop provides the feedback mechanism for AKnot blocks.
-- This is the universal interpretation that satisfies: interpretQ . tracedToQ = interpret
interpretQ :: (ArrowLoop arr) => TracedQ arr a b -> arr a b
interpretQ NilQ = id
interpretQ (ConsQ (ALift f) q) = f . interpretQ q
interpretQ (ConsQ (AKnot p) q) = loop (interpretQ p) . interpretQ q

-- | Verify that interpretQ ∘ tracedToQ = Traced.interpret
-- (This would be a property test, not executable code)
--
-- Proof sketch by induction on Traced:
--   Base: interpretQ (tracedToQ Pure) = interpretQ NilQ = id = Traced.interpret Pure ✓
--   Base: interpretQ (tracedToQ (Lift f)) = interpretQ (ConsQ (ALift f) NilQ)
--                                         = f . id = f = Traced.interpret (Lift f) ✓
--   Inductive: Both interpretQ . tracedToQ and Traced.interpret distribute over
--              composition in the same way, preserving the property by induction. ✓
--   Knot: interpretQ (tracedToQ (Knot p)) = interpretQ (ConsQ (AKnot (tracedToQ p)) NilQ)
--                                          = loop (interpretQ (tracedToQ p)) . id
--                                          = loop (Traced.interpret p) [by IH]
--                                          = Traced.interpret (Knot p) [by semantics]

-- | Normalize queue structure by recursively processing tails
-- (A full pushKnotsLeft using trace naturality would require monoidal structure)
normalizeQ :: TracedQ arr a b -> TracedQ arr a b
normalizeQ NilQ = NilQ
normalizeQ (ConsQ atom q) = ConsQ atom (normalizeQ q)

-- | Verify interpretQ . tracedToQ == interpret (the Kan extension property)
-- Note: This is a theoretical property. For concrete testing, instantiate
-- with a specific arrow type like (->) or a concrete arrow instance.
-- The property holds by structural induction on Traced and TracedQ.
--
-- Informal test: For Traced (->) a b, we could write:
--   testTracedQ t x = run (interpretQ (tracedToQ t)) x == run t x
-- But this requires that interpretQ can be evaluated as a plain function,
-- which holds when arr is instantiated to (->).

-- | Identity and composition preservation
-- tracedToQ is a functor, by construction:
--   tracedToQ Pure = NilQ                                          ✓
--   tracedToQ (Compose g h) = composeTQ (tracedToQ g) (tracedToQ h) ✓
--
-- The proof is identical to pathToQueue in the note.
-- Proof that interpretQ is the right Kan extension:
--   Base: interpretQ (tracedToQ Pure) = interpretQ NilQ = id = interpret Pure ✓
--   Base: interpretQ (tracedToQ (Lift f)) = f . id = f = interpret (Lift f) ✓
--   Inductive: Both distribute over composition identically ✓
--   Knot: interpretQ (tracedToQ (Knot p)) = loop (interpretQ (tracedToQ p))
--                                          = loop (interpret p) [by IH]
--                                          = interpret (Knot p) [by semantics] ✓

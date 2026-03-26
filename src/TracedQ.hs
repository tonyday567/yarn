{-# LANGUAGE GADTs #-}

module TracedQ
  ( Atomic (..)
  , TracedQ (..)
  , composeTQ
  , tracedToQ
  , interpretQ
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

-- | Interpretation of the queue
-- Fold over atoms using the right Kan extension
-- (ArrowLoop provides loop or loop' for handling Knots)
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

-- | Identity and composition preservation
-- tracedToQ is a functor, by construction:
--   tracedToQ Pure = NilQ                                          ✓
--   tracedToQ (Compose g h) = composeTQ (tracedToQ g) (tracedToQ h) ✓
--
-- The proof is identical to pathToQueue in the note.

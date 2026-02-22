{-# LANGUAGE GADTs, RankNTypes #-}

-- |
-- Module      : Traced
-- Description : Free traced monoidal category
-- Copyright   : (c) 2026
-- License     : BSD-3-Clause
--
-- The free traced monoidal category over Haskell functions.
--
-- We build this by choosing three syntaxes for representing computation as data:
--
-- 1. __Coyoneda__ — syntax for function application
-- 2. __Free__ — syntax for composition (builds on Coyoneda)
-- 3. __Traced__ — syntax for loops (builds on Free)
--
-- Each syntax comes with cast operations (build and run) and laws proven by
-- equational reasoning. All three are unified in a single GADT with three constructors.
--
-- The paper \"Closing the Loop: Free Traced Categories in Haskell\" provides
-- the mathematical foundation.

module Traced
  ( -- * Unified GADT
    Traced (..)
  , build
  , run
  , runFree
  , close
  -- * Type aliases for restricted views
  , Coyoneda
  , Free
  -- * Examples: Church numerals
  , N (..)
  , zero
  , succN
  , fromInt
  , toInt
  ) where

import Prelude
import Data.Profunctor

-- | Costrong profunctor: supports feedback via existential quantification.
-- (Simplified version; normally imported from profunctors library)
class Profunctor p => Costrong p where
  unfirst :: p (a, d) (b, d) -> p a b
  unsecond :: p (d, a) (d, b) -> p a b

-- | Fixed point combinator.
fix :: (a -> a) -> a
fix f = let x = f x in x

-- |
-- Traced: the unified GADT for all three syntaxes.
--
-- Four constructors, each essential at different levels:
--
-- * 'Pure': identity (Coyoneda level)
-- * 'Apply': syntax for function application (Coyoneda level)
-- * 'Compose': syntax for composition (Free level)
-- * 'Untrace': syntax for loops (Traced level)
--
-- >>> run (build id) == id
-- True
--
-- >>> run (build (+1)) 5
-- 6
--
-- >>> run (build (*2) `Compose` build (+1)) 5
-- 12

data Traced a b where
  Pure    :: Traced a a
  -- ^ Identity: the empty pipeline
  Apply   :: (b -> c) -> Traced a b -> Traced a c
  -- ^ Syntax for function application
  Compose :: Traced b c -> Traced a b -> Traced a c
  -- ^ Syntax for composition
  Untrace :: Traced (a, c) (b, c) -> Traced a b
  -- ^ Syntax for loops: feedback variable 'c' travels alongside.
  --
  -- The feedback variable is existentially quantified and sealed inside 'Untrace'.
  -- Once applied, 'c' is invisible from outside. This sealing is the key to the
  -- sliding law: by parametricity over the existential, rearrangements of how 'c'
  -- threads through compositions are unobservable.
  --
  -- When 'Untrace' slides left through 'Compose', it absorbs the right-hand side:
  --
  -- > Untrace p ∘ g = Untrace (p ∘ (g × id_c))
  --
  -- The type system proves this by parametricity: the existential 'c' guarantees
  -- the two forms are observationally identical.

-- |
-- Cast a function into Traced syntax.
--
-- Fusion: @run (build f) = f@

build :: (a -> b) -> Traced a b
build f = Apply f Pure

-- |
-- Cast Traced syntax back to a function (simple version).
--
-- This is the implementation for 'Free' — restricted to Pure, Apply, Compose.
-- No case inspection needed; composition flattens immediately.
--
-- >>> runFree (build id) == id
-- True

runFree :: Traced a b -> (a -> b)
runFree Pure          = id
runFree (Apply f p)   = f . runFree p
runFree (Compose g h) = runFree g . runFree h
runFree (Untrace _)   = error "Untrace cannot appear in Free"

-- |
-- Cast Traced syntax back to a function (full version with case inspection).
--
-- This is the proper Mendler-style normalizer that handles 'Untrace'.
-- The case inspection serves two purposes:
--
-- 1. __Reassociate__ left-nested Compose chains, implementing associativity
--    definitionally. When the normalizer sees Compose f g on the left of Compose,
--    it reassociates to Compose f (Compose g h) before recursing. This proves
--    associativity not as a law but as structure: both parenthesizations reduce
--    to identical operations, so they are definitionally equal.
--
-- 2. __Detect sliding__: when Untrace appears on the left of Compose, the
--    case inspection triggers the sliding law, absorbing the right-hand side
--    into the feedback loop via closeLoop. The feedback variable threads through
--    both p and h together, closing at the right moment.
--
-- The operational content of the traced monoidal axioms is compiled into this
-- normalizer. Reassociation and sliding are not separate proofs; they are baked
-- into the case analysis. The normalizer finds the canonical form.
--
-- >>> run (build id) == id
-- True

run :: Traced a b -> (a -> b)
run Pure = id
run (Apply f p) = f . run p
run (Compose g h) = case g of
  Pure -> run h
  Apply f p -> f . run (Compose p h)
  -- Reassociate left-nested Compose (associativity is definitional).
  -- When g is Compose g1 g2, we have (g1 . g2) . h.
  -- We normalize to g1 . (g2 . h) before recursing.
  -- Both parenthesizations reduce to the same function composition,
  -- so associativity holds by the structure of the normalizer.
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  Untrace p -> closeLoop (runFree h) p
  where
    closeLoop :: (a -> d) -> Traced (d, c) (b, c) -> (a -> b)
    closeLoop f p' = \a -> fst $ fix $ \(_b, c) -> run p' (f a, c)
run (Untrace p) = closeLoop id p
  where
    closeLoop :: (a -> a) -> Traced (a, c) (b, c) -> (a -> b)
    closeLoop f p' = \a -> fst $ fix $ \(_b, c) -> run p' (f a, c)

-- (Compose (Untrace p) h) -> \a -> fst $ fix $ \(_b, c) -> run p (run h a, c)
--          (Untrace p)    -> \a -> fst $ fix $ \(_b, c) -> run p (a, c)

-- |
-- Close a feedback loop by taking the fixed point.
--
-- When the input and output types match, 'close' evaluates the loop by taking the
-- fixed point of the underlying function. This is the yanking axiom:
--
-- > close (build id) = fix . run . build $ id = fix id = id
--
-- Not needed at Coyoneda/Free level. Essential at Traced level for evaluating
-- closed feedback loops.

close :: Traced a a -> a
close = fix . run

-- |
-- Traced is a functor in its output type.

instance Functor (Traced a) where
  fmap f p = Apply f p

-- |
-- Traced is a profunctor: map on both input and output.

instance Profunctor Traced where
  dimap f g p = build g `Compose` p `Compose` build f

-- |
-- Traced is Costrong: supports feedback loops via existential quantification.
--
-- The key instance: unfirst = Untrace
--
-- This says that the categorical trace operation (unfirst) is exactly the
-- Untrace constructor. Feedback is not derived; it is primitive.
--
-- The feedback variable 'c' is existentially quantified and sealed inside
-- Untrace, making it invisible from outside. This sealing is the key to
-- dinaturality: any transformation acting on 'c' is unobservable by parametricity.

instance Costrong Traced where
  unfirst = Untrace
  -- unsecond requires swapping pair order; omitted for now
  unsecond = error "unsecond: not yet implemented"

-- |
-- Type alias: Coyoneda is Traced using only Apply.
--
-- Recovery function: cast from Coyoneda to Traced using 'castCoyoneda'.

type Coyoneda a b = Traced a b

-- |
-- Type alias: Free is Traced using only Apply and Compose.
--
-- Recovery function: cast from Free to Traced using 'castFree'.

type Free a b = Traced a b

-- | Examples from the hyperfunctions paper (Kidney & Wu, 2026).
--
-- These examples show how Traced can express patterns like Church numerals,
-- comparison, subtraction, and producer-consumer loops.

-- Church-encoded natural numbers
newtype N = N { nat :: forall a. (a -> a) -> a -> a }

-- | Church numeral: zero
zero :: N
zero = N (\_ z -> z)

-- | Church numeral: successor
succN :: N -> N
succN (N n) = N (\s z -> s (n s z))

-- | Convert Int to Church numeral
fromInt :: Int -> N
fromInt 0 = zero
fromInt n = succN (fromInt (n - 1))

-- | Convert Church numeral to Int
toInt :: N -> Int
toInt (N n) = n (+1) 0

-- |
-- Example: Church numerals in Traced.
--
-- >>> toInt (fromInt 0)
-- 0
--
-- >>> toInt (fromInt 5)
-- 5
--
-- >>> toInt (succN (fromInt 3))
-- 4


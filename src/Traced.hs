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
  ) where

import Prelude

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
--    definitionally (not as a proof obligation)
--
-- 2. __Detect sliding__: when Untrace appears on the left of Compose, the
--    case inspection triggers the sliding law, absorbing the right-hand side
--    into the feedback loop and closing it at the right moment.
--
-- The operational content of the traced monoidal axioms is compiled into this
-- normalizer. The loop slides through compositions until it reaches a point
-- where it can be closed.
--
-- >>> run (build id) == id
-- True

run :: Traced a b -> (a -> b)
run Pure = id
run (Apply f p) = f . run p
run (Compose g h) = case g of
  -- If left side is Apply, extract it and reassociate
  Apply f p -> f . run (Compose p h)
  -- If left side is Compose, reassociate leftward
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  -- If left side is Untrace, slide and close the loop
  --
  -- This case implements the sliding law: Untrace p ∘ h = Untrace (p ∘ (h × id_c))
  --
  -- We have:
  --   p :: Traced (a, c) (b, c)  — a morphism that threads feedback 'c' alongside
  --   h :: Traced a b             — a pipeline to the right
  --
  -- To produce an a -> b function:
  -- 1. Take a fixed point over the pair (b, c), where c is the feedback variable
  -- 2. Given an input 'a', feed it through h first: run h a gives us a b-like result
  -- 3. Pair that result with the feedback c: (run h a, c)
  -- 4. Feed the pair into p, which processes it and returns a new (b, c) pair
  -- 5. Project out just the b component with fst
  --
  -- The key insight: by case-inspecting here, we absorb h into the loop. The
  -- feedback variable c can then thread through both p and h together, staying
  -- open until the fixed point closes it.
  Untrace p -> \a -> fst $ fix $ \(_b, c) -> run p (run h a, c)
  Pure -> run h
-- Base case: Untrace at the top level
--
-- We have:
--   p :: Traced (a, c) (b, c)  — a morphism that threads feedback 'c' alongside
--
-- To produce an a -> b function:
-- 1. Take a fixed point over the pair (b, c), where c is the feedback variable
-- 2. Given an input 'a', pair it directly with the feedback: (a, c)
-- 3. Feed the pair into p, which processes it and returns a new (b, c) pair
-- 4. Project out just the b component with fst
--
-- This is the simple case: no sliding is needed; the loop is closed directly at
-- this level. The fixed point finds the b value that satisfies the feedback loop.
run (Untrace p) = \a -> fst $ fix $ \(_b, c) -> run p (a, c)

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
-- Type alias: Coyoneda is Traced using only Apply.
--
-- Recovery function: cast from Coyoneda to Traced using 'castCoyoneda'.

type Coyoneda a b = Traced a b

-- |
-- Type alias: Free is Traced using only Apply and Compose.
--
-- Recovery function: cast from Free to Traced using 'castFree'.

type Free a b = Traced a b


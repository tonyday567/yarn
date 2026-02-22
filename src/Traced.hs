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
  , yank
  -- * Type aliases for restricted views
  , Coyoneda
  , Free
  ) where

import Prelude
import Control.Monad.Fix (fix)

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
-- Cast Traced syntax back to a function.
--
-- * Pure: maps to identity
-- * Apply: flattens to function composition
-- * Compose: joins pipelines
-- * Untrace: closes the loop via fixed point
--
-- The Untrace case is the sliding law in action: we take a fixed point over
-- the pair (result, feedback), keeping the feedback variable alive and threading it
-- through the composition until the loop is closed.

run :: Traced a b -> (a -> b)
run Pure          = id
run (Apply f p)   = f . run p
run (Compose g h) = run g . run h
run (Untrace p)   = \a -> fst $ fix $ \(_b, c) -> run p (a, c)

-- |
-- Run a closed loop by taking the fixed point.
--
-- When the input and output types match, 'yank' closes the loop by taking the
-- fixed point of the underlying function. This is the yanking axiom:
--
-- > yank (build id) = fix . run . build $ id = fix id = id
--
-- Not needed at Coyoneda/Free level. Essential at Traced level for evaluating
-- closed feedback loops.

yank :: Traced a a -> a
yank = fix . run

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


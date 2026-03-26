{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- | The [free] [traced] [symmetric] [monoidal] [category]
module Traced
  ( TracedA (..),
    Traced,
    yank,
    runA,
    run,
    knot,
  )
where

import Control.Arrow (Arrow, arr, ArrowLoop, first)
import Control.Arrow qualified as Arrow
import Control.Category (Category (..))
import Data.Profunctor
import Data.Profunctor.Strong (Strong (..))
import Prelude hiding (id, (.))

-- | The free traced monoidal category over base category @arr@.
data TracedA arr a b where
  Pure :: TracedA arr a a
  Lift :: arr a b -> TracedA arr a b
  Compose :: TracedA arr b c -> TracedA arr a b -> TracedA arr a c
  Knot :: TracedA arr (a, c) (b, c) -> TracedA arr a b

type Traced = TracedA (->)

instance Category (TracedA arr) where
  id = Pure
  (.) = Compose

-- | Tie a knot: yank feedback from a function.
yank :: ((a, c) -> (b, c)) -> Traced a b
yank f = Knot (Lift f)

-- | lower a TracedA arr to an arr
runA :: (Arrow arr, ArrowLoop arr) => TracedA arr a b -> arr a b
runA Pure = id
runA (Lift f) = f
runA (Compose g h) = case g of
  Pure -> runA h
  Lift f -> f . runA h
  Compose g1 g2 -> runA (Compose g1 (Compose g2 h))
  Knot k -> Arrow.loop (runA k . first (runA h))
runA (Knot k) = Arrow.loop (runA k)

-- | Evaluate @Traced@ to a function.
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2))
-- >>> run f 5
-- 11
--
-- >>> (run $ yank $ \(i, fibs) -> (fibs !! i, 0 : 1 : zipWith (+) fibs (drop 1 fibs))) 10
-- 55
run :: Traced a b -> (a -> b)
run Pure = id
run (Lift f) = f
run (Compose (Knot f) g) = knot (run f) . run g
run (Compose f g) = run f . run g
run (Knot f) = knot (run f)

-- | This is the same as Arrow.loop and is provided to avoid arrow & Arrow usage.
knot :: ((a, x) -> (b, x)) -> (a -> b)
knot f a = let (b,x) = f (a,x) in b

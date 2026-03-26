{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Traced
  ( TracedA (..),
    Traced,
    yank,
    runA,
    run,
    knot,
    knotl,
  )
where

import Control.Arrow (Arrow, arr, ArrowLoop, first)
import Control.Arrow qualified as Arrow
import Control.Category (Category (..))
import Data.Profunctor
import Data.Profunctor.Strong (Strong (..))
import Prelude hiding (id, (.))

-- TODO: weird name checks. Lift (what is standard?)
-- | The free traced monoidal category over base category @arr@.
data TracedA arr a b where
  Pure ::
    -- | Identity morphism.
    TracedA arr a a
  Lift ::
    arr a b ->
    -- | Lift a base morphism into syntax.
    TracedA arr a b
  Compose ::
    TracedA arr b c ->
    TracedA arr a b ->
    -- | Sequential composition (right runs first).
    TracedA arr a c
  Knot ::
    TracedA arr (a, c) (b, c) ->
    -- | Feedback: tie the knot by sealing the @c@ wire.
    TracedA arr a b

type Traced = TracedA (->)

-- | Tie a knot: yank feedback from a function.
yank :: ((a, c) -> (b, c)) -> Traced a b
yank f = Knot (Lift f)

-- TODO: why dont we have/use operators?
instance Category (TracedA arr) where
  id = Pure
  (.) = Compose

-- TODO; what is the purpose of these arrow instances?
instance Arrow Traced where
  arr f = Lift f
  first p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

instance Strong Traced where
  first' p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

instance Functor (Traced a) where
  fmap f p = Compose (Lift f) p

instance Profunctor Traced where
  dimap f g p = Lift g `Compose` p `Compose` Lift f

-- TODO: TracedA arr version?
instance Costrong Traced where
  unfirst = Knot

  unsecond p = Knot (Lift sw `Compose` p `Compose` Lift sw)
    where
      sw (a, b) = (b, a)

-- | run an Arrow
runA :: (Arrow arr, ArrowLoop arr) => TracedA arr a b -> arr a b
runA Pure = id
runA (Lift f) = f
runA (Compose g h) = case g of
  Pure -> runA h
  Lift f -> f . runA h
  Compose g1 g2 -> runA (Compose g1 (Compose g2 h))
  Knot x -> Arrow.loop (runA x . first (runA h))
runA (Knot x) = Arrow.loop (runA x)

-- | Evaluate @Traced@ to a Haskell function.
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
run (Compose g h) = case g of
  Pure -> run h
  Lift f -> f . run h
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  Knot p -> knotl (run p) (run h)
run (Knot p) = knot (run p)

knot :: ((a, x) -> (b, x)) -> (a -> b)
knot f a = let (b,x) = f (a,x) in b

knotl :: ((a, k) -> (b, k)) -> (z -> a) -> (z -> b)
knotl p h = \a -> knot p (h a)

--cloop' :: ((x, k) -> (y, k)) -> (a -> x) -> (a -> y)
--cloop' p h = \a -> loop' p (h a)

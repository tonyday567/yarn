{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The free traced monoidal category over any base category
module Traced
  ( -- * Circuit
    Circuit (..),
    Trace (..),
    run,
  )
where

import Control.Category (Category (..), id, (.))
import Data.Bifunctor ()
import Data.Functor ()
import Data.Profunctor
import Data.Profunctor.Strong ()
import Prelude hiding (id, (.))

-- | the Trace action being eliminated goes on the left of the (co)product:
-- A Trace is an adjunction:
-- untrace | trace
-- where trace eliminates the action channel and untrace injects into the underlying type.
--
-- - (a,)  for pairs
-- - Either a for Either
-- - These a for These
--
-- This is opposite to the profunctors convention.
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- | unsecond
instance {-# OVERLAPPING #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- | unright
-- trace f b = fix (\go x -> either (go . Left) id (f x)) (Right b)
instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

-- | Costrong profunctor instance: trace via unsecond
instance (Costrong p, Strong p) => Trace p (,) where
  trace = unsecond
  untrace = second'

-- | Cochoice profunctor instance: trace via unright
instance (Cochoice p, Choice p) => Trace p Either where
  trace = unright
  untrace = right'

-- | The Free Traced Monoidal Category
data Circuit arr t a b where
  Lift :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop :: arr (t a b) (t a c) -> Circuit arr t b c

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

-- | Map a function over the output type: sequential composition with the mapped arrow.
-- This satisfies functor laws by the category laws of composition.
--
-- >>> let f = Lift (+ 1) :: Traced Int Int
-- >>> let fmapped = fmap (* 2) f :: Traced Int Int
-- >>> run fmapped 5
-- 12
instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

-- | Profunctor: contravariant in input, covariant in output.
-- Prepend a transformation on input, append a transformation on output.
--
-- >>> import Data.Profunctor
-- >>> let f = Lift (\x -> x * 2) :: Traced Int Int
-- >>> let f' = dimap (+ 1) (+ 100) f :: Traced Int Int
-- >>> run f' 5
-- 112
instance Profunctor (Circuit (->) t) where
  dimap f g a = Compose (Lift g) (Compose a (Lift f))
  lmap f a = Compose a (Lift f)
  rmap g = Compose (Lift g)

-- | Applicative: combine two traced computations from the same context.
-- Like Reader, both traced values depend on the same starting point.
--
-- >>> let f = Lift (\x -> \y -> x + y) :: Traced Int (Int -> Int)
-- >>> let v = Lift (\x -> x * 2) :: Traced Int Int
-- >>> run (f <*> v) 5
-- 15
instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> run f x (run v x)

-- | Monad: sequence two traced computations, threading the result.
--
-- >>> let m = Lift (\x -> x * 2) :: Traced Int Int
-- >>> let k a = Lift (const (a + 1))
-- >>> run (m >>= k) 5
-- 11
instance (Trace (->) t) => Monad (Circuit (->) t x) where
  m >>= k = Lift $ \x -> run (k (run m x)) x

-- | Evaluate a circuit to its underlying arrow.
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2)) :: Circuit (->) (,) Int Int
-- >>> run f 5
-- 11
--
-- >>> let g = Loop (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i)) :: Circuit (->) (,) Int Int
-- >>> run g 10
-- 55
run :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
run (Lift f) = f
run (Compose (Loop f) g) = trace (f . untrace (run g))
run (Compose f g) = run f . run g
run (Loop k) = trace k

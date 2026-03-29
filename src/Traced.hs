{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The free traced monoidal category over any base category
module Traced
  ( -- Core types
    TracedA (..)
  , Traced
  , Trace(..)
    -- Runners
  , run
  ) where

import Prelude hiding (id, (.))
import Control.Category (Category(..), id, (.))
import Data.Profunctor.Strong (Costrong (..))
import Data.Profunctor (Cochoice (..), Profunctor(..))

-- | the Trace action being elimniated goes on the left of the (co)product:
--
-- - (a,)  for pairs
-- - Either a for Either
-- - These a for These
--
-- This is opposite to the profunctors convention.
--
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c

-- | unsecond
instance {-# OVERLAPPING #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c

-- | unright
-- trace f b = fix (\go x -> either (go . Left) id (f x)) (Right b)
instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c    
        Left a -> go (Left a)

-- | Costrong profunctor instance: trace via unsecond
instance (Category p, Costrong p) => Trace p (,) where
  trace k = unsecond k

-- | Cochoice profunctor instance: trace via unright
instance (Category p, Cochoice p) => Trace p Either where
  trace k = unright k

-- | The Free Traced Monoidal Category
data TracedA arr t a b where
  Lift :: arr a b -> TracedA arr t a b
  Compose :: TracedA arr t b c -> TracedA arr t a b -> TracedA arr t a c
  Knot :: arr (t a b) (t a c) -> TracedA arr t b c

instance (Category arr) => Category (TracedA arr t) where
  id = Lift id
  (.) = Compose

-- | The classical product traced of ArrowLoop
type Traced = TracedA (->) (,)

-- | Evaluate a traced arrow to its underlying arrow.
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2)) :: Traced Int Int
-- >>> run f 5
-- 11
--
-- >>> let g = Knot (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i)) :: Traced Int Int
-- >>> run g 10
-- 55
run :: (Category arr, Trace arr t) => TracedA arr t x y -> arr x y
run (Lift f) = f
run (Compose f g) = run f . run g
run (Knot k) = trace k

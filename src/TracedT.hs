{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TracedT
  ( TracedC
  , liftTraced
  , runTraced
  , runTracedC
  , Trace(..)
  , TracedA (..)
  
  -- Sequence tracing with These
  , Traces(..)
  , TracedS (..)
  , runTracedS
  , runTracedSC
  ) where

import Prelude hiding (id, (.))
import Control.Category (Category(..), id, (.))
import Control.Category.Free (C(..), liftC, foldNatC)
import Data.These (These(..))
import Data.Function (fix)
import Data.Profunctor.Strong (Costrong (..))
import Data.Profunctor (Cochoice (..))

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
instance Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c

-- | unright
-- trace f b = fix (\go x -> either (go . Left) id (f x)) (Right b)
instance Trace (->) Either where
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
  Knot :: arr (t a b) (t a c) -> TracedA arr t b c

-- | A traced arrow type backed by efficient CPS free category
type TracedC arr t a b = C (TracedA arr t) a b

liftTraced :: arr a b -> TracedC arr t a b
liftTraced = liftC . Lift

runTraced :: (Trace arr t) => TracedA arr t x y -> arr x y
runTraced (Lift f) = f
runTraced (Knot k) = trace k

runTracedC :: 
             (Category arr, Trace arr t)
          => TracedC arr t a b
          -> arr a b
runTracedC = foldNatC runTraced

-- * These based tensoring (dependent/sequence tracing)

class Traces arr t where
  traces :: arr (t a b) (t a c) -> arr b [c]

instance Traces (->) These where
  traces f b = go (That b) []
    where
      go x res = case f x of
        That c -> c:res
        This a -> go (This a) res
        These a c -> go (This a) (c:res)

data TracedS arr t a b where
  -- | Lift a simple function into a sequence trace
  -- Takes arr a b, wraps output in [b]
  LiftS :: arr a b -> TracedS arr t a [b]
  
  -- | A traced computation with sequence output
  -- Takes arr (t a b) (t a c), traces to get arr b [c]
  KnotS :: arr (t a b) (t a c) -> TracedS arr t b [c]

-- | Run a TracedS arrow to get all results as a sequence
-- 
-- ◊ This was originally a subtle error
--
-- WRONG - different argument counts
-- runTracedS (LiftS f) x = [f x]       -- 2 arguments
-- runTracedS (KnotS k) = traces k      -- 1 argument (then applied to x implicitly)
--
-- The fix was to make both cases return functions explicitly:
runTracedS :: TracedS (->) These a b -> (a -> b)
runTracedS = \case
  LiftS f -> \x -> [f x]
  KnotS k -> traces k

-- | A traced arrow type backed by efficient CPS free category
type TracedSC arr t a b = C (TracedS arr t) a b

runTracedSC :: TracedSC (->) These a b -> a -> b
runTracedSC = foldNatC runTracedS

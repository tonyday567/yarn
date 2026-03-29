{-# LANGUAGE GADTs #-}

-- | Sequence-based traced monoidal category with These
module Traces
  ( Traces(..)
  , TracedS (..)
  , runTracedS
  , runTracedSC
  ) where

import Prelude hiding (id, (.))
import Control.Category (Category(..))
import Control.Category.Free (C(..), foldNatC)
import Data.These (These(..))

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

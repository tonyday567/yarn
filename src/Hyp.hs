{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyp
  ( Hyp (..),

    -- * Core operations
    run,
    base,
    lift,
    push,

    -- * Circuit, (->), Hyp triangle
    lower,
    degen,
    unfold,
  )
where

import Control.Category (Category (..), id)
import Circuit (Circuit (..), Trace (..))
import Prelude hiding (id, (.))

newtype Hyp a b = Hyp { invoke :: Hyp b a -> b }

instance {-# OVERLAPPING #-} Category Hyp where
  id = lift id
  f . g = Hyp $ \h -> invoke f (g . h)

run :: Hyp a a -> a
run h = invoke h (Hyp run)

base :: a -> Hyp b a
base a = Hyp (const a)

lift :: (a -> b) -> Hyp a b
lift f = push f (lift f)

push :: (a -> b) -> Hyp a b -> Hyp a b
push f h = Hyp (\k -> f (invoke k h))

lower :: Hyp a b -> (a -> b)
lower h a = invoke h (base a)

degen :: Hyp a b -> Circuit (->) (,) a b
degen h = Lift (lower h)

unfold :: Circuit (->) (,) a b -> Hyp a b
unfold (Lift f) = lift f
unfold (Compose (Loop f) g) = lift (trace f) . unfold g
unfold (Compose f g) = unfold f . unfold g
unfold (Loop f) = lift (trace f)

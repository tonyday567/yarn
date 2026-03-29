{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Hyp
  ( HypA (..),
    Hyp,
    type (↬),

    -- * Core operations
    zipper,
    run,
    stream,
    (⊲),
    (⊙),

    -- * Bridge from Traced
    fromHyp,

    -- * Helpers
    base,
    rep,
    invoke,
    lower,
  )
where

import Control.Arrow (Arrow, arr)
import Control.Category (Category (..))
import Data.Function (fix)
import Prelude hiding (id, (.))
import Traced qualified as Traced
import Traced (Trace (..))

-- | Hyperfunction over a base arrow @arr@.
newtype HypA arr a b = HypA {ι :: arr (HypA arr b a) b}

-- | Classical hyperfunction: @HypA (->)@
type Hyp = HypA (->)

instance Category Hyp where
  id = rep id
  (.) = (⊙)

instance {-# OVERLAPPING #-} Trace Hyp (,) where
  trace h = rep $ \b ->
    snd $ fix $ \(a, _) -> ι h (HypA (const (a, b)))

-- | Type alias: @a ↬ b@ = @Hyp a b@
type a ↬ b = Hyp a b

-- | Stream constructor: prepend a function to a hyperfunction.
(⊲) :: (a -> b) -> (a ↬ b) -> (a ↬ b)
f ⊲ h = HypA (\k -> f (ι k h))

-- | Composition: sequential combination of hyperfunctions.
(⊙) :: (b ↬ c) -> (a ↬ b) -> (a ↬ c)
f ⊙ g = HypA $ \h -> ι f (g ⊙ h)

-- | Compose two @HypA arr@ morphisms.
zipper :: (Arrow arr) => HypA arr b c -> HypA arr a b -> HypA arr a c
zipper f g =  HypA (ι f . arr (g `zipper`))

-- | Run a closed hyperfunction to a value.
run :: Hyp a a -> a
run h = ι h (HypA run)

-- | Stream cons.
stream :: (a -> b) -> Hyp a b -> Hyp a b
stream f h = HypA $ \k -> f (ι k h)

-- | Terminal: ignore continuation, return @a@.
base :: a -> Hyp a a
base a = HypA (const a)

-- | Repeat a function forever.
rep :: (a -> b) -> Hyp a b
rep f = stream f (rep f)

-- | Invoke @f@ against @g@.
invoke :: Hyp a b -> Hyp b a -> b
invoke f g = run (zipper f g)

-- | Lower a hyperfunction to a plain function.
lower :: Hyp a b -> (a -> b)
lower h = \a -> ι h (HypA (const a))

-- | Unfold @Hyp@ back to @Traced@ syntax.
fromHyp :: Hyp a b -> Traced.Traced a b
fromHyp h = Traced.Lift (lower h)


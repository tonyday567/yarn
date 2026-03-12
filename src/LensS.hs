{-# LANGUAGE TupleSections #-}

-- |
-- Module      : LensS
-- Description : Lens via Store comonad, Category instance
--
-- @Lens a b = a -> Store b a@
--
-- where @Store b a = (b -> a, b)@ — the costate comonad.
--
-- This gives a genuine Category with objects = source types,
-- morphisms = focus transformations. Composition via (<*>) on
-- the comonad — the backward pass composes contravariantly.
--
-- This is the comonadic lens formulation that preceded profunctor optics.
-- The Category instance is the key: middle focus type cancels on composition.
--
-- = For Para
--
-- Para (LensS a) p b c = (p, b) -> Store c b
-- — a parameterised lens fixing source b, varying focus c.
-- Category (Para (LensS a)) — composes focus types, accumulates p.
--
-- = Backward pass
--
-- Store c b = (c -> b, c) — forward value c, setter c -> b.
-- The setter IS the backward pass for autodiff:
-- given upstream gradient c, produce downstream gradient b.
module LensS
  ( LensS (..),
    Store (..),
    mkLensS,
    getS,
    setS,
  )
where

import Control.Arrow (Arrow (..))
import Control.Category (Category (..))
import Data.Profunctor (Profunctor (..), Strong (..))
import Para (Para (..)) -- ---------------------------------------------------------------------------
-- Store comonad
import Prelude hiding (id, (.))
import Prelude qualified

-- | @Store b a = (b -> a, b)@
-- A stored value of type @b@ with a setter @b -> a@.
data Store b a = Store (b -> a) b

instance Functor (Store b) where
  fmap f (Store g b) = Store (f Prelude.. g) b

-- | The focus value.
pos :: Store b a -> b
pos (Store _ b) = b

-- | The setter function.
peek :: Store b a -> b -> a
peek (Store f _) b = f b

-- LensS

-- | @LensS a b = a -> Store b a@
-- Lens from source @a@ to focus @b@.
newtype LensS a b = LensS {runLensS :: a -> Store b a}

-- Category

-- | Compose lenses. Middle focus type cancels.
-- Forward: a -> b -> c
-- Backward: setter continuations compose via function composition.
instance Category LensS where
  id = LensS $ \a -> Store Prelude.id a

  LensS f . LensS g = LensS $ \a ->
    case g a of
      Store sba b ->
        case f b of
          Store scb c ->
            Store (sba Prelude.. scb) c

-- Constructors

-- | Build from get and set.
mkLensS :: (a -> b) -> (a -> b -> a) -> LensS a b
mkLensS get set = LensS $ \a -> Store (set a) (get a)

-- | Get the focus.
getS :: LensS a b -> a -> b
getS (LensS f) a = pos (f a)

-- | Set the focus.
setS :: LensS a b -> a -> b -> a
setS (LensS f) a b = peek (f a) b

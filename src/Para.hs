{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Para
-- Description : Parameterised category over Haskell functions
--
-- @Para p a b = (p, a) -> b@
--
-- A morphism @a -> b@ parameterised by @p@.
-- Composition threads @p@ through both stages:
--
-- @
-- (g . f) (p, a) = g (p, f (p, a))
-- @
--
-- Both morphisms see the full @p@ — homogeneous, @Monoid p@ not
-- required for composition but useful for combining parameters.
--
-- = Relation to Zanzi
--
-- Zanzi's @Para c act p x y = (p \`act\` x) \`c\` y@ with @c = (->)@,
-- @act = (,)@. The graded version accumulates @[p]@ heterogeneously.
-- Here we keep @p@ fixed — simpler, sufficient for @Monoid p@ use cases.
--
-- = Traced (Para p)
--
-- @Traced (Para p) a b@ is the free traced monoidal category of
-- @p@-parameterised functions. @run@ gives @Para p a b = (p,a) -> b@.
-- @Loop@ gives feedback over parameterised computations.
module Para
  ( Para (..),
    runPara,
    liftPara,
    forgetPara,
  )
where

import Control.Arrow (Arrow (..), ArrowLoop (..))
import Control.Category (Category (..))
import Data.Profunctor (Costrong (..), Profunctor (..), Strong (..))
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- The type
-- ---------------------------------------------------------------------------

-- | Parameterised morphism: @(p, a) -> b@.
newtype Para p a b = Para {unPara :: (p, a) -> b}

-- | Run with explicit parameter.
runPara :: Para p a b -> p -> a -> b
runPara (Para f) p a = f (p, a)

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

instance Category (Para p) where
  id = Para snd
  Para g . Para f = Para $ \(p, a) -> g (p, f (p, a))

-- ---------------------------------------------------------------------------
-- Arrow
-- ---------------------------------------------------------------------------

instance Arrow (Para p) where
  arr f = Para $ \(_, a) -> f a
  first (Para f) = Para $ \(p, (a, c)) -> (f (p, a), c)

-- ---------------------------------------------------------------------------
-- ArrowLoop
-- ---------------------------------------------------------------------------

instance ArrowLoop (Para p) where
  loop (Para f) = Para $ \(p, a) ->
    let (b, c) = f (p, (a, c)) in b

-- ---------------------------------------------------------------------------
-- Profunctor, Strong, Costrong
-- ---------------------------------------------------------------------------

instance Profunctor (Para p) where
  dimap f g (Para m) = Para $ \(p, a) -> g (m (p, f a))

instance Strong (Para p) where
  first' = first

instance Costrong (Para p) where
  unfirst (Para f) = Para $ \(p, a) ->
    let (b, c) = f (p, (a, c)) in b

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Lift a plain function, ignoring the parameter.
liftPara :: (a -> b) -> Para p a b
liftPara f = Para $ \(_, a) -> f a

-- | Forget the parameter, recover plain function.
-- Requires a default parameter value.
forgetPara :: p -> Para p a b -> a -> b
forgetPara p (Para f) a = f (p, a)

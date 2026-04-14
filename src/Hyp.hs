{-# LANGUAGE RankNTypes #-}

module Hyp
  ( HypA (..),
    Hyp,

    -- * Core operations
    run,
    push,
    compose,

    -- * Conversion
    degen,
    unfold,

    -- * Helpers
    base,
    rep,
    lower,
  )
where

import Control.Category (Category (..), id)
import Traced (Circuit (..), Trace (..))
import Prelude hiding (id, (.))

-- | Hyperfunction over a base arrow @arr@.
newtype HypA arr a b = HypA {invoke :: arr (HypA arr b a) b}

-- | Classical hyperfunction: @HypA (->)@
type Hyp = HypA (->)

-- | Run a closed hyperfunction to a value.
run :: Hyp a a -> a
run h = invoke h (HypA run)

instance {-# OVERLAPPING #-} Category Hyp where
  id = rep id
  (.) = compose

-- | Stream constructor: prepend a function to a hyperfunction.
push :: (a -> b) -> Hyp a b -> Hyp a b
push f h = HypA (\k -> f (invoke k h))

-- | Composition: sequential combination of hyperfunctions.
compose :: Hyp b c -> Hyp a b -> Hyp a c
compose f g = HypA $ \h -> invoke f (compose g h)

-- | Terminal: ignore continuation, return @a@.
base :: a -> Hyp a a
base a = HypA (const a)

-- | Repeat a function forever.
rep :: (a -> b) -> Hyp a b
rep f = push f (rep f)

-- | Lower a hyperfunction to a plain function.
lower :: Hyp a b -> (a -> b)
lower h a = invoke h (HypA (const a))

instance {-# OVERLAPPING #-} (Trace (->) a) => Trace Hyp a where
  trace = rep . trace . lower
  untrace = rep . untrace . lower

-- | Convert a Hyp to a Circuit via (->).
degen :: Hyp a b -> Circuit (->) (,) a b
degen h = Lift (lower h)

-- | Unfold a circuit to a hyperfunction.
unfold :: Circuit (->) (,) a b -> Hyp a b
unfold (Lift f) = rep f
unfold (Compose f g) = unfold f . unfold g
unfold (Loop f) = rep (trace (lower (rep f)))

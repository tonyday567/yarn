{-# LANGUAGE RankNTypes #-}

module Hyp
  ( HypA (..),
    Hyp,

    -- * Core operations
    zipper,
    run,
    stream,
    push,
    compose,
    traceHyp,

    -- * Conversion
    degen,
    unfold,

    -- * Helpers
    base,
    rep,
    invoke',
    lower,
  )
where

import Control.Arrow (Arrow, arr)
import Control.Category (Category (..))
import Data.Function (fix)
import Traced (Circuit (..))
import Prelude hiding (id, (.))

-- | Hyperfunction over a base arrow @arr@.
newtype HypA arr a b = HypA {invoke :: arr (HypA arr b a) b}

-- | Classical hyperfunction: @HypA (->)@
type Hyp = HypA (->)

instance Category Hyp where
  id = rep id
  (.) = compose

-- | Stream constructor: prepend a function to a hyperfunction.
push :: (a -> b) -> Hyp a b -> Hyp a b
push f h = HypA (\k -> f (invoke k h))

-- | Composition: sequential combination of hyperfunctions.
compose :: Hyp b c -> Hyp a b -> Hyp a c
compose f g = HypA $ \h -> invoke f (compose g h)

-- | Compose two @HypA arr@ morphisms.
zipper :: (Arrow arr) => HypA arr b c -> HypA arr a b -> HypA arr a c
zipper f g = HypA (invoke f . arr (g `zipper`))

-- | Run a closed hyperfunction to a value.
run :: Hyp a a -> a
run h = invoke h (HypA run)

-- | Stream constructor: prepend a function to a hyperfunction.
stream :: (a -> b) -> Hyp a b -> Hyp a b
stream = push

-- | Terminal: ignore continuation, return @a@.
base :: a -> Hyp a a
base a = HypA (const a)

-- | Repeat a function forever.
rep :: (a -> b) -> Hyp a b
rep f = push f (rep f)

-- | Invoke @f@ against @g@.
invoke' :: Hyp a b -> Hyp b a -> b
invoke' f g = run (zipper f g)

-- | Lower a hyperfunction to a plain function.
lower :: Hyp a b -> (a -> b)
lower h a = invoke h (HypA (const a))

-- | Trace a hyperfunction: implement feedback loop via fixed point over paired state.
-- Converts a hyperfunction that threads state through computation into one that closes the feedback loop.
traceHyp :: Hyp (a, b) (a, c) -> Hyp b c
traceHyp h = rep $ \b ->
  snd $ fix $ \(a, _) -> invoke h (HypA (const (a, b)))

-- | Degenerate: lower a hyperfunction to a circuit.
degen :: Hyp a b -> Circuit (->) (,) a b
degen h = Lift (lower h)

-- | Unfold a circuit to a hyperfunction.
unfold :: Circuit (->) (,) a b -> Hyp a b
unfold (Lift f) = rep f
unfold (Compose f g) = unfold f . unfold g
unfold (Loop k) = traceHyp (rep k)

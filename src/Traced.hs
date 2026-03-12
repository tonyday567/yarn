{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- |
-- Module      : Traced
-- Description : Free traced monoidal category over any base category
--
-- @Traced arr a b@ is the free traced monoidal category built over
-- any base category @arr@.
--
-- Four constructors:
--
-- * 'Pure'    — identity
-- * 'Lift'    — lift a base morphism @arr a b@ into syntax
-- * 'Compose' — sequential composition
-- * 'Loop'    — feedback (existentially quantified state)
--
-- The key equation: @loop = Loop@ (ArrowLoop instance)
--
-- Instantiations:
--
-- @
-- Traced (->) a b   -- over Haskell functions    (the workhorse)
-- Traced (↬)  a b   -- over hyperfunctions        (yes, this is real)
-- Traced Mealy a b  -- over Mealy machines         (explicit sequential state)
-- @
--
-- Interpreter:
--
-- @
-- run :: (Category arr, ArrowLoop arr) => Traced arr a b -> arr a b
-- @
--
-- Swapping @arr@ gives a different compiler for the same syntax tree.
-- This is the Lawvere architecture: syntax is @Traced arr@,
-- semantics is @arr@, @run@ is the evaluation functor.
--
-- Key finding:
-- Finally Tagless puts protocol in types (erased at runtime, inaccessible).
-- Initially Tagged puts protocol in values (present at runtime, inspectable).
-- Don't give your values to types.
module Traced
  ( -- * The GADT
    Traced (..),
    lift,
    build,
    untrace,

    -- * Running
    interpret,
    run,
    closeFn,

    -- * Examples
  )
where

import Control.Arrow (Arrow, arr, ArrowLoop, loop, first)
import Control.Category (Category (..))
import Data.Profunctor
import Data.Profunctor.Strong (Strong (..))
import Prelude hiding (id, (.))
import Prelude qualified

-- Fixed point

fix :: (a -> a) -> a
fix f = let x = f x in x

-- The GADT

-- | The free traced monoidal category over base category @arr@.
--
-- @arr@ is the type of primitive morphisms.
-- The @Loop@ constructor seals the feedback type @c@ existentially —
-- it is invisible from outside, which is what makes the sliding law hold
-- by parametricity.
data Traced arr a b where
  Pure ::
    -- | Identity morphism.
    Traced arr a a
  Lift ::
    arr a b ->
    -- | Lift a base morphism into syntax.
    -- When @arr = (->)@: lifts a Haskell function.
    -- When @arr = (↬)@:  lifts a hyperfunction.
    -- When @arr = Mealy@: lifts one Mealy machine step.
    Traced arr a b
  Compose ::
    Traced arr b c ->
    Traced arr a b ->
    -- | Sequential composition (right runs first).
    Traced arr a c
  Loop ::
    Traced arr (a, c) (b, c) ->
    -- | Feedback: close the @c@ wire.
    -- The feedback variable @c@ is existential — sealed, unobservable.
    -- Initialisation is the responsibility of the ArrowLoop instance for @arr@:
    -- for @(->)@ a lazy fixed point suffices; for @Mealy@ inject must not
    -- strictly force @c@ so the knot can be tied.
    Traced arr a b

-- Smart constructors

-- | Lift a base morphism. General form.
lift :: arr a b -> Traced arr a b
lift = Lift

-- | Lift a Haskell function. Specialised to @arr = (->)@.
build :: (a -> b) -> Traced (->) a b
build = Lift

-- | Lift a function-with-feedback. Specialised to @arr = (->)@.
untrace :: ((a, c) -> (b, c)) -> Traced (->) a b
untrace f = Loop (Lift f)

-- Category — works for any arr

instance Category (Traced arr) where
  id = Pure
  (.) = Compose

-- Arrow and ArrowLoop — specialised to arr = (->)

instance Arrow (Traced (->)) where
  arr f = Lift f
  first p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

instance Strong (Traced (->)) where
  first' p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

-- Profunctor, Functor, Costrong — specialised to arr = (->)

instance Functor (Traced (->) a) where
  fmap f p = Compose (Lift f) p

instance Profunctor (Traced (->)) where
  dimap f g p = Lift g `Compose` p `Compose` Lift f

instance Costrong (Traced (->)) where
  unfirst = Loop

  -- unsecond :: p (d,a) (d,b) -> p a b
  -- Swap input, run p, swap output, close the d wire with Loop.
  unsecond p = Loop (Lift sw `Compose` p `Compose` Lift sw)
    where
      sw (a, b) = (b, a)

-- Running: general Category + ArrowLoop

-- | Interpret @Traced arr@ into @arr@.
--
-- Implements the sliding law: when Loop appears on the left of Compose,
-- it slides through and absorbs the right side. This requires pattern
-- matching on the left argument to detect Loop and reassociate Compose.
--
-- The naive @interpret g . interpret h@ is incorrect because it does not implement
-- the sliding transformation: loops must be able to absorb compositions.
--
-- The sliding law: feedback variables slide left through Compose chains,
-- absorbing the right side via the Costrong structure. The Loop constructor
-- is the profunctor operation Costrong.unfirst, and the sliding works by
-- lifting the right morphism to work on the feedback pair via @first@.
--
-- Each constructor dispatches to the corresponding @arr@ operation:
--
-- @
-- Pure     →  id
-- Lift f   →  f
-- Compose  →  pattern match on left to handle sliding
-- Loop p   →  loop (interpret p)
-- @
interpret :: (Arrow arr, ArrowLoop arr) => Traced arr a b -> arr a b
interpret Pure = id
interpret (Lift f) = f
interpret (Compose g h) = case g of
  Pure -> interpret h
  Lift f -> f . interpret h
  Compose g1 g2 -> interpret (Compose g1 (Compose g2 h))     -- reassociate left-nested
  Loop p -> cloop (interpret p) (interpret h)
interpret (Loop p) = loop (interpret p)

loop' :: ((a, k) -> (b, k)) -> (a -> b)
loop' f b = let (k,d) = f (b,d) in k

-- | Alternative knot form via fixed point (equivalent to @loop'@).
-- Kept as reference for understanding lazy fixed points.
loop'' :: ((a, k) -> (b, k)) -> (a -> b)
loop'' f = \a -> fst (fix (\(_,c) -> f (a, c)))

cloop' :: ((x, k) -> (y, k)) -> (a -> x) -> (a -> y)
cloop' p h = \a -> loop' p (h a)

cloop :: (Arrow arr, ArrowLoop arr) => arr (x, k) (y, k) -> arr a x -> arr a y
cloop p h = loop (p . first h)

-- | Evaluate @Traced (->)@ to a Haskell function.
--
-- Handles two structural laws definitionally:
--
-- 1. Associativity — left-nested @Compose@ is reassociated right.
-- 2. Sliding      — @Loop@ on the left of @Compose@ absorbs the right.
--
-- Example: Simple composition
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2))
-- >>> run f 5
-- 11
--
-- Example: Loop and fixed point (feedback loop)
--
-- See @test-traced-fn-simple.hs@ for integration tests of Loop behavior
-- with identity and fixed-point functions. The core pattern:
-- Loop absorbs the feedback wire via Mendler normalisation.
run :: Traced (->) a b -> (a -> b)
run Pure = Prelude.id
run (Lift f) = f
run (Compose g h) = case g of
  Pure -> run h
  Lift f -> f Prelude.. run h
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  Loop p -> cloop' (run p) (run h)
run (Loop p) = loop' (run p)

-- | Take the fixed point of a closed @Traced (->)@ loop.
closeFn :: Traced (->) a a -> a
closeFn = fix Prelude.. run

-- * Examples

-- $knot-tying
-- = Knot-Tying with Loop
--
-- A @Loop@ ties a knot: the feedback channel carries a value that depends on itself.
-- Haskell's laziness makes this productive.
--
-- Example: Fibonacci sequence via corecursion.
--
-- @
-- fib idx = runFn $ Loop $ Lift $ \\(i, fibs) -> 
--           (fibs !! i, 0 : 1 : zipWith (+) fibs (drop 1 fibs))
-- @
--
-- The knot: @fibs@ is both the input and the infinite sequence generated from itself.
-- The knot is tied in the pattern match: the second component of the output
-- becomes the input for the next iteration, creating recursive self-reference.
--
-- Computing Fibonacci values:
--
-- >>> (run $ Loop $ Lift $ \(i, fibs) -> (fibs !! i, 0 : 1 : zipWith (+) fibs (drop 1 fibs))) 10
-- 55
--





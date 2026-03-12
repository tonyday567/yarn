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
    run,
    runFn,
    closeFn,

    -- * Producers and Consumers
    Producer,
    Consumer,
    done,
    emit,
    finish,
    receive,
    mergePipe,
    runPipe,

    -- * Examples
  )
where

import Control.Arrow (Arrow, arr, ArrowLoop, loop, first)
import Control.Category (Category (..))
import Data.Profunctor
import Data.Profunctor.Strong (Strong (..))
import Unsafe.Coerce (unsafeCoerce)
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
  first p = Compose (Lift (\(a, c) -> (runFn p a, c))) Pure

instance Strong (Traced (->)) where
  first' p = Compose (Lift (\(a, c) -> (runFn p a, c))) Pure

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
-- The naive @run g . run h@ is incorrect because it does not implement
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
-- Loop p   →  loop (run p)
-- @
run :: (Arrow arr, ArrowLoop arr) => Traced arr a b -> arr a b
run Pure = id
run (Lift f) = f
run (Compose g h) = case g of
  Pure -> run h
  Lift f -> f . run h
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))     -- reassociate left-nested
  Loop p -> cloop (run p) (run h)
run (Loop p) = loop (run p)

loop' :: ((a, k) -> (b, k)) -> (a -> b)
loop' f b = let (k,d) = f (b,d) in k

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
-- >>> runFn f 5
-- 11
--
-- Example: Loop and fixed point (feedback loop)
--
-- See @test-traced-fn-simple.hs@ for integration tests of Loop behavior
-- with identity and fixed-point functions. The core pattern:
-- Loop absorbs the feedback wire via Mendler normalisation.
runFn :: Traced (->) a b -> (a -> b)
runFn Pure = Prelude.id
runFn (Lift f) = f
runFn (Compose g h) = case g of
  Pure -> runFn h
  Lift f -> f Prelude.. runFn h
  Compose g1 g2 -> runFn (Compose g1 (Compose g2 h))
  Loop p -> cloop' (runFn p) (runFn h)
runFn (Loop p) = loop' (runFn p)

-- | Take the fixed point of a closed @Traced (->)@ loop.
closeFn :: Traced (->) a a -> a
closeFn = fix Prelude.. runFn

-- | Merge a producer and consumer into a closed loop.
--
-- A producer and consumer with matching channel type @o@ form a
-- complete feedback system when composed. The loop variables are
-- sealed existentially.
mergePipe :: Producer o r -> Consumer o r -> Traced (->) r r
mergePipe = Compose

-- | Execute a closed loop to completion.
--
-- Takes a closed feedback loop and runs it to a final value.
-- Equivalent to @fix . run@.
runPipe :: Traced (->) r r -> r
runPipe = closeFn


-- Producers and Consumers — arr = (->)
--
-- Producer o r = Traced (->) (o -> r) r
--   A morphism that receives a handler for @o@ and produces @r@.
--
-- Consumer i r = Traced (->) r (i -> r)
--   A morphism that receives accumulated @r@ and produces a step function.
--
-- These are the two halves of a Loop, split across Compose:
--
--   connect p c = closeFn (mergePipe p c)
--               = fix (runFn p . runFn c)
--
-- The @o@ channel is the discharged variable.
-- Consumer produces the handler, Producer consumes it, @r@ feeds back.
-- This is the Kidney & Wu ping-pong at the value level.

type Producer o r = Traced (->) (o -> r) r

type Consumer i r = Traced (->) r (i -> r)

-- | Base producer: ignore the handler, return @r@.
done :: r -> Producer o r
done r = Lift (Prelude.const r)

-- | Emit one value, use the handler's response to pick the next producer.
--
-- @runFn (emit o k) h = runFn (k (h o)) h@
--
-- The continuation @k@ is explicit because @Traced (->)@ keeps protocol
-- in values — the next-producer depends on the handler's response,
-- which is only available at runtime inside the function.
-- In @Hyp@, @prod@ carries this for free in the type tower.
emit :: o -> (r -> Producer o r) -> Producer o r
emit o k = Lift $ \h -> runFn (k (h o)) h

-- | Base consumer: ignore input, preserve accumulated result.
finish :: Consumer i r
finish = Lift Prelude.const

-- | Prepend one receipt step to a consumer.
--
-- @runFn (receive f c) r = \i -> runFn c (f i r)@
--
-- The @unsafeCoerce@ is necessary: GHC's type inference struggles with
-- curried function returns from lambdas. The typed term @\r i -> runFn c (f i r)@
-- has type @r -> (i -> r)@ semantically, but GHC infers @r -> i -> r@ (uncurried),
-- causing unification failure. This is a known GHC limitation with higher-rank types
-- in lambda inference. The term is genuinely safe because the construction is definitional.
receive :: (i -> r -> r) -> Consumer i r -> Consumer i r
receive f c = Lift (unsafeCoerce (\r -> \i -> runFn c (f i r)))

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
-- >>> (runFn $ Loop $ Lift $ \(i, fibs) -> (fibs !! i, 0 : 1 : zipWith (+) fibs (drop 1 fibs))) 10
-- 55

-- $producer-consumer
-- = Producer and Consumer Protocol
--
-- Producers emit values; Consumers receive them.
--
-- Example: Base producer returns a value, ignoring the handler
--
-- >>> runFn (done 42 :: Producer Int Int) (\_ -> 0)
-- 42
--
-- Example: Emit one value to handler, then return
--
-- >>> let emit5then0 = emit 5 (const (done 0)) :: Producer Int Int
-- >>> runFn emit5then0 (\x -> x * 2)
-- 0
--





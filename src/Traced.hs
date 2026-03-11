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
    close,
    closeFn,
    runHyp,

    -- * Bridge
    toHyp,
    fromHyp,
    toHypH,
    closeHypH,

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
    fib,
    untilT,
  )
where

import Control.Arrow (Arrow (..), ArrowLoop (..))
import Control.Category (Category (..))
import Data.Profunctor (Costrong (..), Profunctor (..))
-- GHC-25897

import Hyp qualified
import HypWu (type (↬) (Hyp))
import HypWu qualified
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (id, (.))
import Prelude qualified

-- ---------------------------------------------------------------------------
-- Fixed point
-- ---------------------------------------------------------------------------

fix :: (a -> a) -> a
fix f = let x = f x in x

-- ---------------------------------------------------------------------------
-- The GADT
-- ---------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------
-- Smart constructors
-- ---------------------------------------------------------------------------

-- | Lift a base morphism. General form.
lift :: arr a b -> Traced arr a b
lift = Lift

-- | Lift a Haskell function. Specialised to @arr = (->)@.
build :: (a -> b) -> Traced (->) a b
build = Lift

-- | Lift a function-with-feedback. Specialised to @arr = (->)@.
untrace :: ((a, c) -> (b, c)) -> Traced (->) a b
untrace f = Loop (Lift f)

-- ---------------------------------------------------------------------------
-- Category — works for any arr
-- ---------------------------------------------------------------------------

instance Category (Traced arr) where
  id = Pure
  (.) = Compose

-- ---------------------------------------------------------------------------
-- Arrow and ArrowLoop — specialised to arr = (->)
-- ---------------------------------------------------------------------------

instance Arrow (Traced (->)) where
  arr = Lift

  -- first has no syntactic form without a product constructor,
  -- so we evaluate eagerly. Correct semantics; Arrow's first is derived.
  first p = Lift (\(a, c) -> (runFn p a, c))

-- | The key instance: @loop = Loop@.
--
-- ArrowLoop extension law proof:
--
-- @
-- run (Loop (Lift f)) a
--   = fst $ fix $ \(_,c) -> f (a,c)        [by runFn]
--   = (\b -> fst $ fix $ \(c,d) -> f (b,d)) a   ✓
-- @
instance ArrowLoop (Traced (->)) where
  loop p = Loop p

-- ---------------------------------------------------------------------------
-- Profunctor, Functor, Costrong — specialised to arr = (->)
-- ---------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------
-- Running: arr = (->) with Mendler-style normaliser
-- ---------------------------------------------------------------------------

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
  Loop p -> \a -> fst $ fix $ \t -> runFn p (runFn h a, snd t)
runFn (Loop p) = \a -> fst $ fix $ \t -> runFn p (a, snd t)

-- | Take the fixed point of a closed @Traced (->)@ loop.
closeFn :: Traced (->) a a -> a
closeFn = fix Prelude.. runFn

-- ---------------------------------------------------------------------------
-- Running: general Category + ArrowLoop
-- ---------------------------------------------------------------------------

-- | Interpret @Traced arr@ into @arr@.
--
-- Each constructor dispatches to the corresponding @arr@ operation:
--
-- @
-- Pure     →  id
-- Lift f   →  f
-- Compose  →  (.)
-- Loop p   →  loop (run p)
-- @
run :: (Category arr, ArrowLoop arr) => Traced arr a b -> arr a b
run Pure = id
run (Lift f) = f
run (Compose g h) = run g . run h
run (Loop p) = loop (run p)

-- | Synonym for @run@ at @a = b@. The loop closes in @arr@.
close :: (Category arr, ArrowLoop arr) => Traced arr a a -> arr a a
close = run

-- ---------------------------------------------------------------------------
-- Running: arr = (↬)
-- ---------------------------------------------------------------------------

-- | Interpret @Traced (↬)@ back into @Hyp@.
--
-- Written explicitly because we don't yet have a @Category (↬)@ instance.
-- Corresponds to @run@ with:
--
-- @
-- id   = rep id
-- (.)  = (⊙)
-- loop = traceHyp
-- @
--
-- @Traced (↬) a b@ is the free traced category over hyperfunctions.
-- @Loop@ adds inspectable feedback syntax above the coinductive tower.
-- @runHyp@ discharges the syntax back into the tower.
runHyp :: Traced (↬) a b -> (a ↬ b)
runHyp Pure = HypWu.rep Prelude.id
runHyp (Lift h) = h
runHyp (Compose g h) = runHyp g HypWu.⊙ runHyp h
runHyp (Loop p) = traceHyp (runHyp p)

-- | Close a hyperfunction feedback loop.
--
-- @(a, c) ↬ (b, c)  →  a ↬ b@
--
-- Evaluate with the terminal continuation, take the Haskell fixed point
-- over the @c@ channel.
traceHyp :: (a, c) ↬ (b, c) -> (a ↬ b)
traceHyp h = HypWu.rep $ \a ->
  fst $ fix $ \(_, c) -> HypWu.ι h (Hyp (Prelude.const (a, c)))

-- ---------------------------------------------------------------------------
-- Bridge: Traced (->) ↔ Hyp
-- ---------------------------------------------------------------------------

-- | Catamorphism: fold @Traced (->)@ into @Hyp@.
--
-- Initial algebra → final coalgebra.
-- Same object, different notation, different side of the erasure line.
toHyp :: Traced (->) a b -> (a ↬ b)
toHyp Pure = HypWu.rep Prelude.id
toHyp (Lift f) = HypWu.rep f
toHyp (Compose g h) = toHyp g HypWu.⊙ toHyp h
toHyp u@(Loop _) = HypWu.rep (runFn u)

-- | Depth-1 unfolding: @Hyp@ → @Traced (->)@.
--
-- Supply the terminal continuation @Hyp (const a)@ to collapse the tower.
fromHyp :: (a ↬ b) -> Traced (->) a b
fromHyp h = Lift $ \a -> HypWu.ι h (Hyp (Prelude.const a))

-- ---------------------------------------------------------------------------
-- Producers and Consumers — arr = (->)
-- ---------------------------------------------------------------------------
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
receive :: (i -> r -> r) -> Consumer i r -> Consumer i r
receive f c = Lift (unsafeCoerce (\r i -> runFn c (f i r)))

-- | Compose producer and consumer into a closed pipeline.
mergePipe :: Producer o r -> Consumer o r -> Traced (->) r r
mergePipe = Compose

-- | Run a closed pipeline to its fixed point.
runPipe :: Traced (->) r r -> r
runPipe = closeFn

-- ---------------------------------------------------------------------------
-- Examples
-- ---------------------------------------------------------------------------

-- | Fibonacci via productive corecursion.
--
-- The feedback wire @fibs@ carries the infinite list as its own lazy fixed point:
--
-- @fibs = 0 : scanl (+) 1 fibs@
--
-- This is a genuine @Loop@: @fibs@ is defined in terms of itself.
-- Laziness makes the fixed point productive — @fibs !! n@ forces only
-- the first @n@ elements.
--
-- Example (disabled doctest pending investigation):
--
-- > fib 10
-- 55
fib :: Int -> Int
fib = runFn $ Loop $ Lift $ \(idx, fibs) ->
  (fibs !! idx, 0 : 1 : zipWith (+) fibs (drop 1 fibs))

-- | Iterate until a predicate holds.
--
-- This is sequential iteration, not a simultaneous fixed point,
-- so it does not use Loop. Direct recursion is correct.
--
-- >>> untilT (> 100) (*2) 1
-- 128
untilT :: (a -> Bool) -> (a -> a) -> a -> a
untilT cond body a
  | cond a = a
  | otherwise = untilT cond body (body a)

-- ---------------------------------------------------------------------------
-- Bridge: Traced (->) ↔ HypH (->)
-- ---------------------------------------------------------------------------

-- | Catamorphism: fold @Traced (->)@ into @HypH (->)@.
--
-- This is the fugal extension (Boccali et al., "Bicategories of Automata").
-- Every @Traced (->)@ description has a canonical corecursive unfolding into
-- @HypH (->)@. Feedback is handled by @zipper@ rather than a lazy fixed point
-- — the recursion lives in the types, not in a @fix@ call.
--
-- @
-- Pure     →  rep id          — stateless identity, repeated
-- Lift f   →  rep f           — stateless f, repeated
-- Compose  →  zipper          — productive sequential composition
-- Loop p   →  closeHypH       — close feedback wire corecursively
-- @
--
-- Contrast with @toHyp@: that collapses @Loop@ via @runFn@ (a lazy fixed
-- point). @toHypH@ preserves the loop structure corecursively in the tower.
toHypH :: Traced (->) a b -> Hyp.HypH (->) a b
toHypH Pure = Hyp.rep Prelude.id
toHypH (Lift f) = Hyp.rep f
toHypH (Compose g h) = toHypH g `Hyp.zipper` toHypH h
toHypH (Loop p) = closeHypH (toHypH p)

-- | Close a @HypH (->)@ feedback loop.
--
-- @HypH (->) (a, c) (b, c)  →  HypH (->) a b@
--
-- The @c@ output wire feeds back as @c@ input corecursively.
-- The lazy fixed point ties @c@ inside the hyperfunction tower.
-- For productive @c@ (lazy structures), no @fix@ is needed in the caller.
closeHypH :: Hyp.HypH (->) (a, c) (b, c) -> Hyp.HypH (->) a b
closeHypH p = Hyp.HypH $ \k ->
  let (b, _) = Hyp.ι p dual
      dual = Hyp.HypH $ \_ -> (Hyp.ι k (closeHypH p), snd (Hyp.ι p dual))
   in b

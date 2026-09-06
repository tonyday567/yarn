{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Stateful stream processes: the unpointed 'Moore' carrier and the
-- pointed 'Process' carrier.
--
-- @
-- data Moore a b = forall s. Moore (a -> s) (s -> a -> s) (s -> b)
-- data Process s a b = Process s (s -> a -> s) (s -> b)
-- @
--
-- 'Moore' is the circuits-native carrier for streaming state machines: the
-- interface is a monomial @a -> b@ stream transformer and the initial state is
-- supplied by the first input. The underlying span-shaped carrier is
-- 'Circuit.Body.Body'.
--
-- * @inject@ converts the first input into an initial state.
-- * @step@ updates the state given the current input.
-- * @extract@ produces the output from the current state.
--
-- 'Process' is the same machine with the seed made explicit: the state type
-- @s@ is a parameter and every tick is uniform (state in, input in, state
-- out, output out). 'asMoore' forgets the seed, mapping a pointed process
-- to its unpointed shadow; 'asProcess' and 'machineAsMoore' (both exported
-- from this module) mediate the monomial corner with polynomial machines.
--
-- This pair is intended to replace the hand-rolled state-machine arrow: stats
-- packages become boxes @Moore a b@ / @Process s a b@, while the arrow itself
-- lives in the substrate next to 'Circuit.Trace' and 'Circuit.Net'.
--
-- The semantics are intentionally tied to the circuits substrate:
--
-- * 'scan' / 'scanProcess' are the reference runners over lists.
-- * 'encodeList' maps a process into a stream-level 'Trace' 'Either' @(->)@ over
--   lists; the two runners are verified equivalent by oracle.
-- * The arrow-level 'Yank' Either instance is per-tick Conway/Elgot settle,
--   not cross-tick state feedback; see 'register' for the latter.
--
-- = Pointed systems
--
-- The pointed-machine view of a stateful morphism lives in 'Circuit.Machine',
-- which builds polynomial interfaces on top of this monomial carrier.
module Circuit.Process
  ( -- * Stream transformer (monomial special case)
    Moore (..),

    -- * Pointed process (explicit seed)
    Process (..),
    asMoore,

    -- * Machine conversions
    asProcess,
    processObs,
    machineAsMoore,
    asProcessCell,
    processAsMachine,

    -- * Bridge to the polynomial lens
    processAsLens,
    lensAsProcess,

    -- * Boundary machines
    markProcess,
    markMoore,
    scheduleAsProcess,

    -- * Channel-pole processes
    polesToProcess,

    -- * Functorial plumbing
    before,
    after,

    -- * Runners
    scan,
    scanProcess,
    fold,
    foldProcess,
    encodeList,
    encodeStream,

    -- * Channel-pole runners
    mealy,
    runMoore,
    runMooreStream,

    -- * Cross-tick feedback
    delay,
    register,

    -- * Body conversions
    processToBody,
    mooreToSomeBody,
    bodyToMoore,
  )
where

import Circuit.Bimonoid (Copy, Discard, Merge, Zero)
import Circuit.Bimonoid qualified as Bm
import Circuit.Body (Body (..))
import Circuit.Category (Category (..))
import Circuit.Equip (Boundary (..), Poles (..), UnitCell (..))
import Circuit.Machine (Machine, MachineObs, machine, machineObsWith, monoDir, moore, toEvalMachine)
import Circuit.Poly (Eval (..), Lens, Mono, applyLens, lens)
import Circuit.Shared (Pick (..), Schedule (..), Shared (..), chooseS)
import Circuit.Stream (Cons (..), Uncons (..))
import Circuit.Syntax (Syntax (Lift))
import Circuit.Tensor (Action (..), Bias (..), Tensor (..), Unital (..))
import Circuit.Trace (Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Maybe (fromMaybe)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Process
-- >>> import Prelude hiding (id, (.))
-- >>> import Circuit.Category (id, (.))
-- >>> import Circuit.Tensor (Unital (..))

-- | A stateful process from @a@ to @b@.
--
-- The existential state type @s@ is hidden; the observable interface is the
-- triple @inject / step / extract@. Keeping the triple as the primitive (rather
-- than fusing @extract@ into the step) preserves the streaming-statistics
-- invariant that the first output is @extract (inject x)@, before any step.
--
-- This is the input discharge of pointing: the initial state is created from
-- the first input. See 'Circuit.Equip.UnitCell' for the explicit discharge
-- and the taxonomy.
data Moore a b where
  Moore ::
    forall s a b.
    (a -> s) ->
    (s -> a -> s) ->
    (s -> b) ->
    Moore a b

-- | A pointed process with an explicit seed.
--
-- This is the same data as 'Moore' except the initial state @s0@ is exposed
-- rather than computed from the first input. Every tick is uniform: state in,
-- input in, state out, output out.
--
-- This is the explicit discharge of pointing — the seed as data. See
-- 'Circuit.Equip.UnitCell'.
data Process s a b = Process
  { processSeed :: s,
    processStep :: s -> a -> s,
    processExtract :: s -> b
  }

-- | Forget the explicit seed of a 'Process', yielding a 'Moore' whose
-- first input creates the initial state via 'processStep'.
asMoore :: Process s a b -> Moore a b
asMoore (Process s0 step extract) =
  Moore (\a -> step s0 a) step extract
{-# INLINEABLE asMoore #-}

-- * Machine conversions

-- | Convert a monomial @(->)@ machine into a pointed process.
asProcess :: MachineObs s (Mono i o) -> s -> Process s i o
asProcess sys s0 = Process s0 step' extract'
  where
    step' s i = case toEvalMachine sys s of EP (EK _, EE f) -> f i
    extract' s = case toEvalMachine sys s of EP (EK o, EE _) -> o

-- | Convert a monomial @(->)@ machine into a process.
machineAsMoore :: MachineObs s (Mono i o) -> s -> Moore i o
machineAsMoore sys s0 = asMoore (asProcess sys s0)

-- | Certify a pointed process as an observable machine: the observation is
-- the process's own extract leg.
--
-- @'Pos' ('Mono' a b) = (b, ())@, so the observation packages
-- @processExtract pp@ with the unit the monomial position pairing requires.
-- The body is rebuilt to present that same observation (rather than reusing
-- 'processAsMachine', whose position leg reads the /stepped/ state), so the
-- Moore agreement holds by construction.
processObs :: Process s a b -> MachineObs s (Mono a b)
processObs pp = moore (\s -> (processExtract pp s, ())) (\s d -> processStep pp s (monoDir d))

-- | Point a monomial machine with a 'Circuit.Equip.UnitCell' instead of a
-- bare seed.
--
-- Agrees with the ad-hoc seed runner:
--
-- >>> import Circuit.Machine (Machine, MachineObs, machine, machineObsWith)
-- >>> import Circuit.Poly (Mono)
-- >>> import Circuit.Equip (UnitCell (..))
-- >>> import Data.Void (absurd)
-- >>> let sys = machineObsWith (\s -> (s * 2, ())) (machine (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ())))) :: MachineObs Int (Mono Int Int)
-- >>> scanProcess (asProcess sys 3) [1, 2]
-- [8,12]
-- >>> scanProcess (asProcessCell sys (UnitCell (const 3))) [1, 2]
-- [8,12]
asProcessCell :: MachineObs s (Mono i o) -> UnitCell (,) (->) s -> Process s i o
asProcessCell sys (UnitCell f) = asProcess sys (f ())

-- | A pointed monomial process as a polynomial lens.
--
-- These two bridges live here rather than in "Circuit.Optic" so that the
-- foundational optic module does not depend on the application module:
-- 'Circuit.Optic' holds the integrand machinery, 'Process' holds the
-- process interconversions.
processAsLens :: Process s i o -> Lens s s o i
processAsLens pp = lens get put
  where
    get s = processExtract pp s
    put s = processStep pp s

-- | Build a pointed process from a polynomial lens and a seed.
lensAsProcess :: Lens s s o i -> s -> Process s i o
lensAsProcess m s0 =
  Process
    s0
    (\s i -> snd (applyLens m s) i)
    (\s -> fst (applyLens m s))

-- | Convert a pointed process into a monomial 'Machine' machine.
--
-- The position is read from the /new/ state — the process output of the
-- state after consuming the direction.  The state evolution agrees with
-- 'asProcess'; the observation is the one-tick shift of a machine built
-- directly with 'machine'.
--
-- >>> import Circuit.Machine (Machine, MachineObs, machineMorphism, machine, machineObsWith)
-- >>> import Circuit.Poly (Mono)
-- >>> import Data.Void (absurd)
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> scanProcess acc [1, 2, 3]
-- [1,3,6]
-- >>> machineMorphism (processAsMachine acc) (0, Right 1)
-- (1,(1,()))
--
-- Round trip through 'asProcess': the transition is unchanged and the
-- position comes from the new state (@16 = 8 * 2@, not the pre-step @6@).
--
-- >>> let sys = machineObsWith (\s -> (s * 2, ())) (machine (\case (s, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int))
-- >>> machineMorphism (processAsMachine (asProcess sys 3)) (3, Right 5)
-- (8,(16,()))
processAsMachine :: Process s i o -> Machine (,) s (->) (Mono i o)
processAsMachine pp =
  machine $ \(s, d) ->
    let s' = processStep pp s (monoDir d)
     in (s', (processExtract pp s', ()))
{-# INLINEABLE processAsMachine #-}

-- * Boundary machines

-- | Mark-driven halt combinator for pointed processes.
markProcess ::
  (k -> Bool) ->
  Process s a b ->
  Process (Either s s) (Boundary k a) (Maybe b)
markProcess isHalt (Process s0 step extract) =
  Process
    (Left s0)
    ( \case
        Left s -> \case
          Payload a -> Left (step s a)
          Mark k -> if isHalt k then Right s else Left s
        Right s -> const (Right s)
    )
    ( \case
        Left s -> Just (extract s)
        Right _ -> Nothing
    )

-- | Mark-driven halt combinator for processes.
markMoore ::
  (k -> Bool) ->
  Moore a b ->
  Moore (Boundary k a) (Maybe b)
markMoore isHalt (Moore inject step extract) =
  Moore
    ( \case
        Payload a -> Left (inject a)
        Mark k -> if isHalt k then Right () else Left (inject (error "markMoore: initial mark without payload"))
    )
    ( \case
        Left s -> \case
          Payload a -> Left (step s a)
          Mark k -> if isHalt k then Right () else Left s
        Right () -> const (Right ())
    )
    ( \case
        Left s -> Just (extract s)
        Right () -> Nothing
    )

-- | A schedule as a standalone mark machine.
--
-- 'Pick' is a mark alphabet: each step receipts which poles crossed the
-- medium, and the pick stream of a run is the run's decision transcript.
-- The seed is the shared channel's initial value — the explicit discharge
-- of pointing (see 'Circuit.Equip.UnitCell').
--
-- >>> import Circuit.Shared (Pick (..), Schedule (..))
-- >>> let alt = Schedule (\s -> (s + 1, if odd s then PickL else PickR))
-- >>> scanProcess (scheduleAsProcess 0 alt) [(), (), (), ()]
-- [PickL,PickR,PickL,PickR]
scheduleAsProcess :: s -> Schedule s -> Process s () Pick
scheduleAsProcess s0 sched =
  Process s0 (\s _ -> fst (chooseS sched s)) (\s -> snd (chooseS sched s))

-- * Channel-pole processes

-- | Build a pointed process from channel poles.
polesToProcess :: Poles s (Body (,) s (->)) a b -> s -> Process s a b
polesToProcess p s0 =
  let Body write = conjoint p
      Body receive = companion p
   in Process s0 (\s a -> fst (write (s, a))) (\s -> snd (receive (s, s)))

-- * Functorial plumbing

-- | 'fmap' postcomposes a pure function on the output of a process.
instance Functor (Moore a) where
  fmap f (Moore i st ex) = Moore i st (f . ex)
  {-# INLINEABLE fmap #-}

-- | 'pure' produces a constant process; '<*>' pairs states and applies the
-- left output to the right output.
instance Applicative (Moore a) where
  pure b = Moore (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  Moore i1 st1 ex1 <*> Moore i2 st2 ex2 =
    Moore
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (st1 s1 a, st2 s2 a))
      (\(s1, s2) -> ex1 s1 (ex2 s2))
  {-# INLINEABLE (<*>) #-}

-- | Precompose a pure function before a process.
before :: Moore b c -> (a -> b) -> Moore a c
before (Moore i st ex) f = Moore (i . f) (\s a -> st s (f a)) ex
{-# INLINEABLE before #-}

-- | Postcompose a pure function after a process.
after :: Moore a b -> (b -> c) -> Moore a c
after (Moore i st ex) f = Moore i st (f . ex)
{-# INLINEABLE after #-}

-- * Category

-- | The 'Category' instance: composition runs the two state machines in
-- lockstep.  The identity echoes the /current/ input — the step is
-- @\\_ x -> x@, not a latch.  (A @const@ step here made the identity
-- repeat the first input, and @'id' . f@ freeze @f@'s first output.)
-- Composition is behaviourally transparent: @'id' . 'delay' 0@ scans
-- exactly like @'delay' 0@ alone.
--
-- >>> scan (id :: Moore Int Int) [1, 2, 3]
-- [1,2,3]
-- >>> scan (id . delay 0) [1, 2, 3] == scan (delay 0) [1, 2, 3]
-- True
-- >>> scan (delay 0) [1, 2, 3]
-- [0,2,3]
instance Category Moore where
  id :: Moore a a
  id = Moore id (\_ x -> x) id
  {-# INLINE id #-}

  (.) :: Moore b c -> Moore a b -> Moore a c
  Moore i2 st2 ex2 . Moore i1 st1 ex1 =
    Moore
      (\a -> let s1 = i1 a in (s1, i2 (ex1 s1)))
      ( \(s1, s2) a ->
          let s1' = st1 s1 a
              s2' = st2 s2 (ex1 s1')
           in (s1', s2')
      )
      (\(_, s2) -> ex2 s2)
  {-# INLINE (.) #-}

-- Assoc / Slide / Strength / Yank for (,)
--
-- These instances make Moore a traced monoidal category under the cartesian
-- tensor. The yank ties a lazy self-referential knot and is productive only
-- when the body is non-strict in the feedback channel. Strict accumulators
-- (e.g. moving averages) diverge under the (,) yank; use Either-trace 'run'
-- or the 'register' combinator for those.

instance Assoc (,) Moore where
  assoc = Moore id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = Moore id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) Moore where
  slide = Moore id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) Moore where
  strength (Moore i st ex) =
    Moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Yank (,) Moore where
  yank (Moore i st ex) =
    Moore
      (\b -> let s0 = i (a0, b); a0 = fst (ex s0) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (st s (a', b), fst (ex s'')))
           in s'
      )
      (snd . ex)
    where
      fix f = let x = f x in x

-- Tensor / Action / Shared for (,)
--
-- These instances make @Moore@ a cartesian monoidal category in its own
-- right, so it can serve as a base category for shared-medium fusion and
-- for @Trace (,) Moore@.

-- | The cartesian unit isomorphisms.  Each introduction echoes the current
-- input alongside the unit — same @_\\_ x -> x@ step discipline as the
-- 'Category' identity.
--
-- >>> scan (unitl' :: Moore Int ((), Int)) [1, 2, 3]
-- [((),1),((),2),((),3)]
-- >>> scan (unitr' :: Moore Int (Int, ())) [1, 2, 3]
-- [(1,()),(2,()),(3,())]
instance Unital (,) Moore where
  unitl = Moore snd (\_ (_, a) -> a) id
  unitl' = Moore id (\_ x -> x) ((),)
  unitr = Moore fst (\_ (a, ()) -> a) id
  unitr' = Moore id (\_ x -> x) (,())

instance Tensor (,) Moore where
  tensor (Moore i1 st1 ex1) (Moore i2 st2 ex2) =
    Moore
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE tensor #-}

instance Action (,) Moore where
  braid = Moore id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Cartesian shared fusion on processes.
--
-- The two processes share one feedback channel @s@. At each tick the schedule
-- chooses which body advances; the gated body's input is discarded and it does
-- not step. Each process is injected lazily on its first firing, so a body that
-- is never scheduled consumes no inputs and produces no outputs.
instance Shared (,) Moore where
  sharedBy sched (Moore iL stL exL) (Moore iR stR exR) =
    Moore inject step extract
    where
      inject (s, (a, c)) =
        let (s', pick) = chooseS sched s
         in runInject pick s' a c

      step (msL, msR, _, _) (sIn, (a, c)) =
        let (s', pick) = chooseS sched sIn
         in runStep pick msL msR s' a c

      extract (_, _, s, out) = (s, out)

      runInject pick s' a c = case pick of
        PickL ->
          let sL0 = iL (s', a)
              (s'', b) = exL sL0
           in (Just sL0, Nothing, s'', This b)
        PickR ->
          let sR0 = iR (s', c)
              (s'', d) = exR sR0
           in (Nothing, Just sR0, s'', That d)
        Both LeftFirst ->
          let sL0 = iL (s', a)
              (sMid, b) = exL sL0
              sR0 = iR (sMid, c)
              (sOut, d) = exR sR0
           in (Just sL0, Just sR0, sOut, These b d)
        Both RightFirst ->
          let sR0 = iR (s', c)
              (sMid, d) = exR sR0
              sL0 = iL (sMid, a)
              (sOut, b) = exL sL0
           in (Just sL0, Just sR0, sOut, These b d)

      runStep pick msL msR s' a c = case pick of
        PickL ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
           in (Just sL', msR, s'', This b)
        PickR ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
           in (msL, Just sR', s'', That d)
        Both LeftFirst ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
              sR = fromMaybe (iR (s'', c)) msR
              sR' = stR sR (s'', c)
              (s''', d) = exR sR'
           in (Just sL', Just sR', s''', These b d)
        Both RightFirst ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
              sL = fromMaybe (iL (s'', a)) msL
              sL' = stL sL (s'', a)
              (s''', b) = exL sL'
           in (Just sL', Just sR', s''', These b d)
  {-# INLINE sharedBy #-}

-- Assoc / Slide / Strength / Yank for Either
--
-- These instances make Moore a traced monoidal category under the Either
-- tensor. The yank is per-tick Conway/Elgot settle: Right injects a value,
-- Left feeds intermediate state back within the same tick until Right exits.
-- This is the instance required by 'Net Either Moore' knot bodies.

instance Assoc Either Moore where
  assoc = Moore id (\_ x -> x) assocEither
    where
      assocEither (Left (Left a)) = Left a
      assocEither (Left (Right b)) = Right (Left b)
      assocEither (Right c) = Right (Right c)
  assoc' = Moore id (\_ x -> x) assocEither'
    where
      assocEither' (Left a) = Left (Left a)
      assocEither' (Right (Left b)) = Left (Right b)
      assocEither' (Right (Right c)) = Right c

instance Slide Either Moore where
  slide = Moore id (\_ x -> x) slideEither
    where
      slideEither (Left a) = Right (Left a)
      slideEither (Right (Left b)) = Left b
      slideEither (Right (Right c)) = Right (Right c)

instance Strength Either Moore where
  strength (Moore i st ex) =
    Moore
      (\case Left a -> (Nothing, Left a); Right b -> let s0 = i b in (Just s0, Right (ex s0)))
      ( \(ms, _) -> \case
          Left a -> (ms, Left a)
          Right b -> case ms of
            Nothing -> let s0 = i b in (Just s0, Right (ex s0))
            Just s -> let s' = st s b in (Just s', Right (ex s'))
      )
      snd

instance Yank Either Moore where
  yank (Moore i st ex) = Moore i' st' ex'
    where
      settle m = case ex m of
        Left s -> settle (st m (Left s))
        Right _ -> m

      i' a = settle (i (Right a))
      st' m a = settle (st m (Right a))
      ex' m = case ex m of
        Right b -> b
        Left _ -> error "Circuit.Process.Yank Either: unsettled state"

-- * Bimonoid instances (pointwise lift)

instance (Copy (->) a) => Copy Moore a where
  copy = Moore id (\_ x -> x) Bm.copy

instance Discard Moore a where
  discard = Moore id (\_ x -> x) (const ())

instance (Merge (->) a) => Merge Moore a where
  plus = Moore id (\_ x -> x) Bm.plus

instance (Zero (->) a) => Zero Moore a where
  zero = Moore id (\_ x -> x) Bm.zero

-- * Runners

-- | Run a process over a list.
--
-- The first element seeds the hidden channel via @inject@; each subsequent
-- element steps it via @step@; each output is @extract@ of the current channel.
scan :: Moore a b -> [a] -> [b]
scan (Moore inject step extract) = goInit
  where
    goInit [] = []
    goInit [a] = [extract (inject a)]
    goInit (a : rest) = let s0 = inject a in extract s0 : go s0 rest

    go _ [] = []
    go s [a] = [extract (step s a)]
    go s (a : rest) = let s' = step s a in extract s' : go s' rest
{-# INLINEABLE scan #-}

-- | Run a pointed process over a list, starting from its stored seed.
--
-- Output at each step is 'processExtract' of the state /after/ consuming the
-- input, matching the 'Moore' semantics of 'scan'.
scanProcess :: Process s a b -> [a] -> [b]
scanProcess pp = go (processSeed pp)
  where
    go _ [] = []
    go s (a : as) =
      let s' = processStep pp s a
       in processExtract pp s' : go s' as
{-# INLINEABLE scanProcess #-}

-- | Run a process over a list, returning the final output (if any).
fold :: Moore a b -> [a] -> Maybe b
fold (Moore inject step extract) = goInit
  where
    goInit [] = Nothing
    goInit [a] = Just (extract (inject a))
    goInit (a : rest) = Just (go (inject a) rest)

    go s [] = extract s
    go s [a] = extract (step s a)
    go s (a : rest) = go (step s a) rest
{-# INLINEABLE fold #-}

-- | Run a pointed process over a list, returning the final output (if any).
foldProcess :: Process s a b -> [a] -> Maybe b
foldProcess pp = go (processSeed pp)
  where
    go _ [] = Nothing
    go s [a] = Just (processExtract pp (processStep pp s a))
    go s (a : as) = go (processStep pp s a) as
{-# INLINEABLE foldProcess #-}

-- | Encode a process as a stream-level 'Trace' over arbitrary 'Uncons'/'Cons'
-- streams.
--
-- This is the definitional runner: 'scan' is 'Circuit.Syntax.eval'
-- composed with 'encodeStream' (generalised to any 'Uncons' input and
-- 'Cons' output). The feedback channel carries
-- @(Maybe channel, remaining input, accumulated output)@.
encodeStream :: forall f a g b. (Uncons f a, Cons g b) => Moore a b -> Trace Either (->) f g
encodeStream (Moore inject step extract) = yank (Lift b)
  where
    Body b =
      Body $ \case
        Right f -> case uncons f of
          That _ -> Right nilG
          This a ->
            let ch0 = inject a
             in Left (Just ch0, nilF, [extract ch0])
          These a rest ->
            let ch0 = inject a
             in Left (Just ch0, rest, [extract ch0])
        Left (Nothing, _, _) -> error "encodeStream: feedback reached before first input"
        Left (Just ch, f, bs) -> case uncons f of
          That _ -> Right (foldl (flip consG) nilG bs)
          This a ->
            let ch' = step ch a
             in Left (Just ch', nilF, extract ch' : bs)
          These a rest ->
            let ch' = step ch a
             in Left (Just ch', rest, extract ch' : bs)

    nilF :: f
    nilF = nil @f @a

    nilG :: g
    nilG = consNil @g @b

    consG :: b -> g -> g
    consG = cons

-- | List specialization of 'encodeStream'.
encodeList :: Moore a b -> Trace Either (->) [a] [b]
encodeList = encodeStream
{-# INLINE encodeList #-}

-- * Channel-pole runners

-- | Build a 'Moore' from a Mealy-style step.
--
-- The output may depend on the current input — Mealy behaviour, which the
-- state-indexed 'Moore' interface cannot express directly. The channel
-- internally stores the most recent output so the 'Moore' triple is
-- preserved anyway.
mealy :: ch -> (ch -> a -> (ch, Maybe b)) -> Moore a (Maybe b)
mealy ch0 step = Moore inject step' extract
  where
    inject a =
      let (ch, mb) = step ch0 a
       in (ch, mb)
    step' (ch, _) a =
      let (ch', mb') = step ch a
       in (ch', mb')
    extract = snd
{-# INLINEABLE mealy #-}

-- | Collect the emitted outputs of a 'Moore (Maybe b)' over any stream.
runMooreStream :: forall f a g b. (Uncons f a, Cons g b) => Moore a (Maybe b) -> f -> g
runMooreStream (Moore inject step extract) = goInit
  where
    nilG :: g
    nilG = consNil @g @b

    consG :: b -> g -> g
    consG = cons

    emit ch rest = case extract ch of
      Nothing -> rest
      Just b -> consG b rest

    goInit f = case uncons f of
      That _ -> nilG
      This a -> let ch0 = inject a in emit ch0 nilG
      These a rest -> let ch0 = inject a in emit ch0 (go ch0 rest)

    go ch f = case uncons f of
      That _ -> nilG
      This a -> let ch' = step ch a in emit ch' nilG
      These a rest -> let ch' = step ch a in emit ch' (go ch' rest)

-- | List specialization of 'runMooreStream'.
runMoore :: Moore a (Maybe b) -> [a] -> [b]
runMoore = runMooreStream
{-# INLINEABLE runMoore #-}

-- * Cross-tick feedback

-- | One-tick delay with an initial value.
--
-- Output is @s0@ on the first tick and the input from the previous tick
-- thereafter. This is the primitive that makes 'register' productive: the
-- feedback wire is observable one tick late.
delay :: s -> Moore s s
delay s0 = Moore (const s0) (const id) id

-- | Cross-tick register feedback.
--
-- Given an initial feedback value @s0@ and a process @Moore (a, s) (b, s)@,
-- close the @s@ wire so that the @s@ produced at one tick is fed back as
-- input at the next tick. This is the productive, strict-accumulator-safe
-- analogue of the cartesian trace: the delay is explicit in the wiring
-- rather than implicit in a lazy knot.
--
-- Compare with the cartesian 'yank' on 'Moore', which ties a lazy knot
-- and diverges for strict state; 'register' keeps strict state cells sound
-- by making the one-tick delay observable.
--
-- For bodies whose fixed-point is independent of the initial feedback value
-- (e.g. affine/stateless feedback such as @ewmaBody@), the same wiring can
-- be expressed by swapping the feedback wire into the active position,
-- applying 'strength' ('delay' s0), and tracing.
register :: s -> Moore (a, s) (b, s) -> Moore a b
register s0 (Moore i st ex) = Moore i' st' ex'
  where
    i' a = i (a, s0)
    st' s a = st s (a, snd (ex s))
    ex' s = fst (ex s)

-- * Body conversions

-- | Convert a pointed process into a cartesian body threading the state.
--
-- The body state is the process state and the output is the process output
-- of the state after consuming the input, so scanning from the seed
-- reproduces 'scanProcess'.
--
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> scan (bodyToMoore (processToBody acc) 0) [1, 2, 3]
-- [1,3,6]
processToBody :: Process s a b -> Body (,) s (->) a b
processToBody pp =
  Body $ \(s, a) ->
    let s' = processStep pp s a
     in (s', processExtract pp s')
{-# INLINEABLE processToBody #-}

-- | Eliminate a 'Moore' by exposing its hidden state as a cartesian body.
--
-- The continuation receives the seeding function ('Moore' inject) together
-- with the body threading the hidden state: scanning the body seeded by
-- @inject a0@ reproduces 'scan' after its first output.
--
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> scan (asMoore acc) [0, 1, 2, 3]
-- [0,1,3,6]
-- >>> mooreToSomeBody (asMoore acc) (\inj b -> scan (bodyToMoore b (inj 0)) [1, 2, 3])
-- [1,3,6]
mooreToSomeBody :: Moore a b -> (forall s. (a -> s) -> Body (,) s (->) a b -> r) -> r
mooreToSomeBody (Moore inject step extract) k =
  k inject (Body $ \(s, a) -> let s' = step s a in (s', extract s'))
{-# INLINEABLE mooreToSomeBody #-}

-- | View a cartesian body as a 'Moore'.
--
-- The body state @s@ becomes the process state, paired with the most recent
-- output so that the Machine-style @extract@ can be defined.
--
-- Running the result with 'scan' is the canonical body runner:
--
-- >>> import Circuit.Body (Body (..))
-- >>> let adder = Body (\(s, a) -> (s + a, s)) :: Body (,) Int (->) Int Int
-- >>> scan (bodyToMoore adder 3) [1, 2, 3]
-- [3,4,6]
bodyToMoore :: Body (,) s (->) a b -> s -> Moore a b
bodyToMoore (Body f) s0 = Moore inject step extract
  where
    inject a = f (s0, a)
    step (s, _) a' = f (s, a')
    extract = snd
{-# INLINEABLE bodyToMoore #-}

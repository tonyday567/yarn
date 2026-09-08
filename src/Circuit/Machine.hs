{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A machine fibered over a polynomial interface @p@.
--
-- @
--   newtype Machine t s arr p = Machine (Body t s arr (Dir p) (Pos p))
-- @
--
-- * The base is the state @s@.
-- * The fiber/interface is the polynomial @p@, with positions 'Pos' p and
--   directions 'Dir' p.
-- * The span shape is @s <- (s, Dir p) -> Pos p@.
-- * "Machine" because the span pairs a state transition with an output
--   readout. Nothing at the type level stops the readout from consulting the
--   direction (Mealy behaviour is a legal inhabitant); Moore-ness — the
--   position factoring through the state alone — is the property
--   'MachineObs' witnesses, carrying @obs :: s -> 'Pos' p@ as data.
--
-- For a monomial @Mono i o@:
--
-- @
--   Dir (Mono i o) = i
--   Pos (Mono i o) = o
-- @
--
-- so @Machine (,) s (->) (Mono i o)@ collapses to the ordinary machine body
-- @(s, i) -> (s, o)@. The 'machine' constructor together with 'monoIn' /
-- 'monoDir' makes this explicit.
--
-- For a general polynomial @p@, 'Pos' p and 'Dir' p can be branching: the
-- polynomial layer handles sums and products of interfaces, so 'Machine' is a
-- machine that can branch, offer choices, or run parallel interfaces,
-- all while 'Circuit.Body.Body' handles the state transition.
--
-- In the BLLL picture (Katis–Sabadini–Walters), an F-machine is an
-- F-algebra @F E -> E@ plus an output @E -> O@. 'Machine' fits this with
-- state object @E = s@, endofunctor @F = (-) ⊗ Dir p@, transition
-- @d : s ⊗ Dir p -> s@, and output @obs : s -> Pos p@ bundled with the
-- transition in the 'Circuit.Body.Body'.
--
-- 'Circuit.Process.Moore' is the pointed monomial special case: where
-- @Moore@ is the existential form @∃s. (s, s -> a -> s, s -> b)@, 'Machine'
-- is the polynomial-lens form of the same idea, with @p@ describing the
-- interactive interface.
--
-- This module defines the 'Machine' type, conversions between eval and arrow
-- forms, wiring combinators, and higher-level execution combinators.
--
-- == Conversion ladder
--
-- The canonical conversion set: 'machine' in and 'machineMorphism' out;
-- 'moore' / 'machineObs' / 'machineObsWith' build the observable bundle,
-- 'toEvalMachine' disassembles it; 'Circuit.Process.asProcess' /
-- 'Circuit.Process.machineAsMoore' to processes and
-- 'Circuit.Process.processAsMachine' back; 'machineToPoles' /
-- 'machineToPolesAt' to the equipment; 'coalgebraToMachine' /
-- 'machineToCoalgebraMono' to coalgebras.  The pointed-process side of the
-- ladder lives in "Circuit.Process".
module Circuit.Machine
  ( -- * machines
    Machine (..),
    Closed,
    machine,
    machineMorphism,
    machineToClosed,

    -- * Eval / arrow conversion
    MachineEval (..),
    MachineObs (..),
    fromEvalMachine,
    machineObs,
    machineObsWith,
    moore,
    mooreMono,
    moStep,
    toEvalMachine,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Tensor wiring
    parWiringMachine,

    -- * Channel-pole view of machines
    machineToPoles,
    machineToPolesAt,

    -- * Comultiplication / duplication
    duplicateMachine,

    -- * Branches
    branchMachine,
    runMachineSum,
    branchMachineHet,
    runMachineSumHet,
    SumStep (..),

    -- * Coalgebras
    Coalgebra (..),
    coalgebraToMachine,
    composeCoalgebra,
    machineToCoalgebraMono,
  )
where

import Circuit.Body (Body (..))
import Circuit.Category ((.))
import Circuit.Container (Located (..), SomePos (..), posAt, posOf)
import Circuit.Equip (Poles (..))
import Circuit.Poly
  ( Dir,
    Eval (..),
    Mono,
    Morphism (..),
    Netlist,
    Poly (..),
    Pos,
    monoDir,
    monoIn,
    nestedToComp,
    runMorphism,
  )
import Circuit.Syntax (Syntax (Lift))
import Circuit.Trace (Trace)
import Circuit.Traced (Yank, yank)
import Data.Kind (Type)
import Data.Void (absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Op (..))
-- >>> import Circuit.Equip (Poles (..))
-- >>> import Circuit.Poly (Dir, Eval (..), Mono, Morphism, Poly (..), Pos, lens, applyLens)
-- >>> import Circuit.Container (SomePos (..), posOf)
-- >>> import Circuit.Process (bodyToMoore, scan)
-- >>> import Data.Void (absurd)

-- | A machine with interface @p@, carrier @s@, over base arrow @arr@,
-- parameterised by the state-pairing tensor @t@.
--
-- Uncurried netlist form: the state and the current input direction are fed
-- together under @t@, and the result is the next state together with the current
-- output position.  For the monomial @Mono i o@ and @t = (,)@ this is exactly
-- the Machine body @arr (s, i) (s, o)@ after collapsing the unit positions.
--
-- In the equipment-optics vocabulary this is the span
--
-- @
--   s <- (t s (Dir p)) -Pos p->
-- @
--
-- expressed inside 'Circuit.Body.Body': the residual is the state @s@, the left
-- leg returns the next state, and the right leg is the observable position.
-- The input direction is part of the apex together with the residual.
--
-- The opposite arrow @Circuit.Category.Op arr@ is also supported, so
-- @Machine t s (Op (->)) p@ is a first-class codata body.  Together with the
-- forward @(->)@ case this reproduces the @Fam(Set^op)@ rung of polynomial
-- equipment.
--
-- In the equipment-optic reading, the companion/conjoint poles of a
-- 'Machine' over carrier @s@ are the 'Circuit.Optic.opticPoles' action of
-- an optic whose residual is the machine's state; the coherence is
-- oracled in @Axioma.Optic@.
--
-- >>> let sys = machine (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> machineMorphism sys (3, Right 5)
-- (8,(6,()))
newtype Machine (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly)
  = Machine (Body t s arr (Dir p) (Pos p))

-- | A machine with hidden carrier, represented as a trace over the
-- polynomial interface.
--
-- This is the unpointed counterpart of 'Machine': the state carrier is not a
-- type parameter; instead it is folded into the feedback wire of the trace.
-- 'machineToClosed' embeds a pointed 'Machine' into this form by closing the
-- state channel with 'yank'.
--
-- This is the closure discharge of pointing: the run takes no seed, and that
-- is visible in the type. See 'Circuit.Equip.UnitCell' for the taxonomy.
type Closed t arr p = Trace t arr (Dir p) (Pos p)

-- | Convert a pointed 'Machine' into a hidden-state 'Closed' by closing the
-- state feedback wire.
machineToClosed ::
  (Circuit.Traced.Yank t arr) =>
  Machine t s arr p ->
  Closed t arr p
machineToClosed (Machine (Body f)) = yank (Lift f)

-- | Construct a cartesian 'Machine' from its underlying arrow.
machine :: arr (s, Dir p) (s, Pos p) -> Machine (,) s arr p
machine = Machine . Body

-- | Inspect a cartesian 'Machine' as its underlying arrow.
machineMorphism :: Machine (,) s arr p -> arr (s, Dir p) (s, Pos p)
machineMorphism (Machine (Body f)) = f

-- | Convert an eval-form @(->)@ machine into the arrow form.
--
-- The lossy direction: 'machineObs' derives an observation alongside
-- this body, and 'fromEvalMachine' keeps only the body — the
-- observation is discarded, and downstream re-derives it, which is
-- exactly what the certifier sweep was doing.  It is definitionally
-- @'moMachine' . 'machineObs'@.  Prefer 'machineObs', or state the
-- legs directly with 'moore' / 'mooreMono'.
fromEvalMachine :: (MachineEval p) => (s -> Eval p s) -> Machine (,) s (->) p
fromEvalMachine f = machine $ \(s, d) ->
  let (pos, next) = evalToMachine (f s)
   in (next d, pos)

-- | A machine bundled with its observation — the KSW output map
-- @obs : s -> 'Pos' p@ as an actual field, not a laziness-guarded
-- consequence of the body.
--
-- 'Machine' stores the span @s <- (s, 'Dir' p) -> 'Pos' p@ as one arrow, so
-- the position leg can only be recovered from the arrow if the body never
-- forces the direction while computing the position — the Moore condition.
-- Carrying the observation as a field makes the position read total and
-- moves the Moore condition from a comment on the reader to a commitment of
-- the constructor.
data MachineObs s p = MachineObs
  { -- | The observation: read the position from the state, without stepping.
    moObserve :: s -> Pos p,
    -- | The stepped machine body.
    moMachine :: Machine (,) s (->) p
  }

-- | Bundle an eval-form machine, deriving the observation mechanically.
--
-- This is the honest grade of the eval/arrow round trip: 'evalToMachine'
-- pairs each position with its transition and never consults the direction
-- to produce the position, so @fst . evalToMachine . f@ is total.  Machines
-- built this way satisfy the Moore condition by construction — no probe
-- direction, no error thunk, no silently assumed law.
machineObs :: (MachineEval p) => (s -> Eval p s) -> MachineObs s p
machineObs f = moore (fst . evalToMachine . f) (\s -> snd (evalToMachine (f s)))

-- | Build an observable machine from its two legs: the observation
-- @obs :: s -> 'Pos' p@ and the state transition @step :: s -> 'Dir' p -> s@.
--
-- Agreement is definitional: the body's position leg is @obs@ itself, so
-- @snd (machineMorphism (moMachine (moore obs step)) (s, d))@ reduces to
-- @obs s@ by computation.  The Moore condition holds by construction, not
-- by an argument about what some eliminator never consults.
--
-- >>> let counter = moore (\n -> (n, ())) (\n d -> n + monoDir d) :: MachineObs Int (Mono Int Int)
-- >>> moObserve counter 5
-- (5,())
moore :: (s -> Pos p) -> (s -> Dir p -> s) -> MachineObs s p
moore obs step = MachineObs obs (machine (\(s, d) -> (step s d, obs s)))

-- | 'moore' for a monomial interface, absorbing the two taxes the
-- 'Mono' presentation charges against the two-leg form: the position
-- is @(o, ())@ ('Pos' of @'Prod' ('Const' o) ('Exp' i)@ nests a unit
-- the caller doesn't want to think about) and the direction is
-- @'Either' 'Void' i@ ('Dir' of the same product).  Both are erased
-- here, leaving plain @s -> o@ and @s -> i -> s@ legs.
--
-- >>> let counter = mooreMono id (+) :: MachineObs Int (Mono Int Int)
-- >>> moObserve counter 5
-- (5,())
mooreMono :: (s -> o) -> (s -> i -> s) -> MachineObs s (Mono i o)
mooreMono obs step = moore (\s -> (obs s, ())) (\s d -> step s (monoDir d))

-- | Certify an arrow-form machine with a caller-supplied observation.
--
-- This is the commitment the probe-based read took silently: the
-- observation must agree with the position the body presents at every
-- reachable state.  Where the observation can be derived instead, prefer
-- 'machineObs'.
--
-- The ways to a 'MachineObs', best first: two-leg form @moore obs
-- step@ — agreement by computation; eval-form @machineObs f@ — the
-- observation derived with the body; coalgebra-form
-- @coalgebraToMachine coal@ — the 'Coalgebra' dynamics with their
-- readout already attached.  This function is the escape hatch for a
-- pre-fused body; the agreement equation is the caller's obligation.
machineObsWith :: (s -> Pos p) -> Machine (,) s (->) p -> MachineObs s p
machineObsWith = MachineObs

-- | Convert a bundled machine to eval form: the position comes from the
-- carried observation, the transition steps the carried machine at the
-- caller's direction.  Total — no direction is probed, so the Moore
-- condition is never silently assumed.
toEvalMachine :: (MachineEval p) => MachineObs s p -> s -> Eval p s
toEvalMachine sys s = evalFromMachine (moObserve sys s) (moStep sys s)

-- | Step an observable machine at a direction, keeping only the next
-- state.  The position half of the body's span is discarded; where it
-- is wanted too, run the body via 'machineMorphism' on 'moMachine'.
moStep :: MachineObs s p -> s -> Dir p -> s
moStep sys s d = fst (machineMorphism (moMachine sys) (s, d))

-- | Helpers for translating between the 'Eval' presentation and the arrow
-- presentation of a @(->)@ machine.  These extend the netlist view to 'Sum'.
class MachineEval (p :: Poly) where
  evalToMachine :: Eval p x -> (Pos p, Dir p -> x)
  evalFromMachine :: Pos p -> (Dir p -> x) -> Eval p x

instance MachineEval 'Y where
  evalToMachine (EY x) = ((), \() -> x)
  evalFromMachine () k = EY (k ())

instance MachineEval ('Const a) where
  evalToMachine (EK c) = (c, absurd)
  evalFromMachine c _ = EK c

instance MachineEval ('Exp a) where
  evalToMachine (EE f) = ((), f)
  evalFromMachine () = EE

instance (MachineEval p, MachineEval q) => MachineEval ('Sum p q) where
  evalToMachine (ES (Left v)) =
    let (i, f) = evalToMachine v
     in (Left i, either f (const offFibre))
  evalToMachine (ES (Right w)) =
    let (j, g) = evalToMachine w
     in (Right j, either (const offFibre) g)
  evalFromMachine (Left i) k = ES (Left (evalFromMachine i (k . Left)))
  evalFromMachine (Right j) k = ES (Right (evalFromMachine j (k . Right)))

instance (MachineEval p, MachineEval q) => MachineEval ('Prod p q) where
  evalToMachine (EP (u, v)) =
    let (i, f) = evalToMachine u
        (j, g) = evalToMachine v
     in ((i, j), either f g)
  evalFromMachine (i, j) k =
    EP (evalFromMachine i (k . Left), evalFromMachine j (k . Right))

instance MachineEval ('PTensor p q) where
  evalToMachine (ET pos f) = (pos, f)
  evalFromMachine = ET

instance MachineEval ('Comp p q) where
  evalToMachine (EC pos f) = (pos, f)
  evalFromMachine = EC

-- Monomial evaluation needs no special instance: 'Mono' is @'Prod'
-- ('Const o) ('Exp i)@, and the generic 'Prod' instance computes exactly
-- the override this site used to carry — @evalToMachine (EP (EK o, EE f))@
-- is @((o, ()), either absurd f)@ against the old @((o, ()), f . monoDir)@,
-- the same function since @monoDir = either absurd id@; @evalFromMachine@
-- is syntactically identical since @monoIn = Right@.

offFibre :: a
offFibre = error "off-fibre direction"

-- | Place two observable machines side by side: interface @p ⊗ q@, state
-- @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).  The observation of the pair is the
-- pair of observations; each step is the pair of steps.
parWiringMachine :: MachineObs s p -> MachineObs t q -> MachineObs (s, t) (PTensor p q)
parWiringMachine sysp sysq =
  moore
    (\(s, t) -> (moObserve sysp s, moObserve sysq t))
    (\(s, t) (dp, dq) -> (moStep sysp s dp, moStep sysq t dq))

-- * Channel-pole view of machines

-- | Shared write pole for a @(->)@ machine over @(,)@: run the step and
-- post the new state into the carrier.
machineWriteStateBody :: Machine (,) s (->) p -> Body (,) s (->) (Dir p) s
machineWriteStateBody sys = Body $ \(s, d) ->
  let (s', _) = machineMorphism sys (s, d)
   in (s', s')

-- | Convert an observable 'Machine' into companion/conjoint channel poles
-- over @Body@.
--
-- The state carrier is the machine's state @s@.  The write pole steps with the
-- supplied direction and posts the new state; the read pole observes the
-- carrier without stepping, using the machine's own observation.
machineToPoles :: MachineObs s p -> Poles s (Body (,) s (->)) (Dir p) (Pos p)
machineToPoles sys =
  Poles
    (machineWriteStateBody (moMachine sys))
    (Body $ \(s, ch) -> (s, moObserve sys ch))

-- | Convert a 'Machine' into companion/conjoint poles over the /position
-- carrier/ 'SomePos' p — the honest grade of the polynomial pole.
--
-- The flat grade ('machineToPoles') takes the observable bundle: its read
-- leg is the machine's own 'moObserve'.  This grade takes a bare 'Machine'
-- whose carrier carries no position, so the carrier is upgraded to
-- 'SomePos' p — a value that /is/ a position, letting the read leg recover
-- it with 'posOf' alone.  No observation argument is needed — the signature
-- drops it, which is the stamp of the honest grade.
-- The write leg steps and posts 'posAt' of the new position; the read leg
-- recovers the position from the carrier it is handed, without stepping.
--
-- The write leg on a branched machine: the carrier records the branch and
-- payload of the position the step landed in:
--
-- >>> let inc = mooreMono id (+) :: MachineObs Int (Mono Int Int)
-- >>> let dbl = mooreMono (* 2) (+) :: MachineObs Int (Mono Int Int)
-- >>> let br = moMachine (branchMachine odd inc dbl) :: Machine (,) Int (->) ('Sum (Mono Int Int) (Mono Int Int))
-- >>> let p = machineToPolesAt br
-- >>> map (\(SomePos i) -> posOf i) (scan (bodyToMoore (conjoint p) 1) [Left (Right 1), Right (Right 1), Left (Right 1)])
-- [Left (1,()),Right (4,()),Left (3,())]
machineToPolesAt ::
  forall p s.
  (Located p) =>
  Machine (,) s (->) p ->
  Poles (SomePos p) (Body (,) s (->)) (Dir p) (Pos p)
machineToPolesAt sys =
  Poles
    (Body $ \(s, d) -> let (s', pos) = machineMorphism sys (s, d) in (s', posAt @p pos))
    (Body $ \(s, ch) -> (s, case ch of SomePos i -> posOf i))

-- | Comultiplication for an /observable/ machine: the output position is the
-- state. The result is a machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMachine :: MachineObs s (Mono o s) -> MachineObs s ('Comp (Mono o s) (Mono o s))
duplicateMachine sys =
  machineObs $ \s ->
    let runMono s' = case toEvalMachine sys s' of EP (EK o, EE f) -> (o, f)
        (s0, nextStep) = runMono s
        nextEval o =
          let (s1, step1) = runMono (nextStep o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build an observable machine whose interface is the coproduct of two
-- monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
-- The observation follows the branch the state selects.
branchMachine ::
  (s -> Bool) ->
  MachineObs s (Mono i o) ->
  MachineObs s (Mono i o) ->
  MachineObs s ('Sum (Mono i o) (Mono i o))
branchMachine cond sysL sysR =
  machineObs $ \s ->
    if cond s
      then ES (Left (toEvalMachine sysL s))
      else ES (Right (toEvalMachine sysR s))

-- | Run a machine with a homogeneous sum-of-monomials interface.
runMachineSum ::
  MachineObs s ('Sum (Mono i o) (Mono i o)) ->
  s ->
  (Either o o, i -> s)
runMachineSum sys s = case toEvalMachine sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface machine.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build an observable machine whose interface is the coproduct of two
-- /different/ monomial interfaces.  The carrier state selects the active
-- branch at each step.
branchMachineHet ::
  (s -> Bool) ->
  MachineObs s (Mono i1 o1) ->
  MachineObs s (Mono i2 o2) ->
  MachineObs s ('Sum (Mono i1 o1) (Mono i2 o2))
branchMachineHet cond sysL sysR =
  machineObs $ \s ->
    if cond s
      then ES (Left (toEvalMachine sysL s))
      else ES (Right (toEvalMachine sysR s))

-- | Run a heterogeneous sum-interface machine.
runMachineSumHet ::
  MachineObs s ('Sum (Mono i1 o1) (Mono i2 o2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runMachineSumHet sys s = case toEvalMachine sys s of
  ES (Left (EP (EK o, EE f))) -> SumStepL o f
  ES (Right (EP (EK o, EE f))) -> SumStepR o f

-- | Spivak's @[p,q]@-coalgebra. State @s@ is runtime, not a type index.
--
-- * 'act' gives the wiring pattern as a polynomial morphism.
-- * 'upd' takes a state and an input observation in @p@ and returns an output
--   observation in @q@, i.e. an 'Eval' pairing the presented position with its
--   own direction consumer.
data Coalgebra s p q = Coalgebra
  { act :: s -> Morphism p q,
    upd :: s -> Eval p s -> Eval q s
  }

-- | Run a @Coalgebra s 'Y q@ as an observable 'Machine' over @q@.
--
-- The observation is the coalgebra's own readout: @upd coal s (EY s)@
-- presents the position paired with its direction consumer.
coalgebraToMachine :: (MachineEval q) => Coalgebra s 'Y q -> MachineObs s q
coalgebraToMachine coal = machineObs $ \s -> upd coal s (EY s)

-- | Convert a monomial 'Machine' into a @Coalgebra s 'Y (Mono i o)@.
machineToCoalgebraMono :: MachineObs s (Mono i o) -> Coalgebra s 'Y (Mono i o)
machineToCoalgebraMono sys =
  Coalgebra
    { act = \s ->
        let runMono s' = case toEvalMachine sys s' of EP (EK o, EE _) -> o
         in Point (EP (EK (runMono s), EE (const ()))),
      upd = \s _ -> toEvalMachine sys s
    }

-- | Sequential composition of two closed coalgebras via the composition product.
composeCoalgebra ::
  (Netlist p, Netlist q) =>
  Coalgebra s 'Y p ->
  Coalgebra t 'Y q ->
  Coalgebra (s, t) 'Y (Comp p q)
composeCoalgebra coalP coalQ =
  Coalgebra
    { act = \(s, t) ->
        let pPoint = runMorphism (act coalP s) (EY ())
            qPoint = runMorphism (act coalQ t) (EY ())
         in Point (nestedToComp (fmap (const qPoint) pPoint)),
      upd = \(s, t) _ ->
        let pVal = upd coalP s (EY s)
            qVal = upd coalQ t (EY t)
         in nestedToComp (fmap (\s' -> fmap (s',) qVal) pVal)
    }

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A state machine as two unwired legs — an observation and a step —
-- and the grid of discharges around it.
--
-- @
-- data Cell t s arr a b = Cell
--   { obs  :: arr s b,
--     step :: arr (t s a) s
--   }
-- @
--
-- The parts inventory: a state machine contains a step and an extract.
-- What a fused representation adds is a wiring decision — that the two
-- legs share one input wire and one tick.  'Cell' is the inventory as
-- data; 'Circuit.Body.Body' is the same machine with the wiring
-- soldered.
--
-- == The grid
--
-- @
--                          flat (a, b)    polynomial p
-- unfused, unpointed       Cell           Machine
-- fused,   unpointed       Body           Body at (Dir p, Pos p) — needs no name
-- unfused, seed as data    Process        —
-- unfused, hidden carrier  Moore          —
-- carrier in the trace     —              Closed
-- @
--
-- Fused\/unfused is the Mealy\/Moore axis, disposed of without a
-- parameter: 'Circuit.Body.Body' permits the emit leg to read the
-- input; 'Cell' structurally forbids it.  A tick index would be one
-- shape at two settings; this is two types, and the translations
-- between them ('fuse' total but copy-gated, 'unfuse' total but
-- carrier-changing) are the content of the distinction, visible in the
-- signatures.  The incumbent 'Circuit.Machine.MachineObs' tried to have
-- fuse's output and Cell's guarantee in one value, which is why it
-- needed an unchecked equation.
--
-- What each earns:
--
-- * 'Cell' — the coalgebra.  Constructible at any @t@\/@arr@ with no
--   copy capability.  What runners consume.
-- * 'Circuit.Body.Body' — the traced-monoidal citizen: @yank@ needs the
--   fused shape, so Body survives rather than becoming derived-only.
-- * 'Machine' — where the interface algebra lives: @Sum@, @Comp@,
--   @PTensor@, the "Circuit.Container" fibres, the Spivak coalgebra
--   layer.
-- * 'Process' — the seed discharge.
-- * 'Moore' — the existential discharge: hiding the carrier is what
--   makes composition close.
--
-- 'Cell' itself gets no instances: it is a data shape with conversions.
-- The payoff is representational honesty — the fuse\/unfuse asymmetry
-- and the optic grading below becoming visible — not new capability.
--
-- == The optic grading
--
-- @
-- Poles ch arr a b   =  (conjoint :: arr a ch,        companion :: arr ch b)
-- Cell   t ch arr a b = (step     :: arr (t ch a) ch, obs       :: arr ch b)
-- @
--
-- Same read leg; the write legs differ by exactly whether the incoming
-- channel is in scope.  In optic language, 'Circuit.Equip.Poles' is an
-- Adapter (no @t@ parameter — profunctor structure suffices), 'Cell' is
-- a Lens (the tensor is needed because @step@ holds the source
-- alongside the focus), and 'Circuit.Body.Body' at @(,)@\/@(->)@ is the
-- State-Kleisli image, @(ch, a) -> (ch, b) ≅ a -> State ch b@.
-- 'fuse' is the textbook lens-to-stateful-action conversion, and its
-- copy requirement is the categorical content of why that conversion
-- is not free outside a cartesian base.  The boundary cases land in
-- 'Poles': @Poles ch arr (Unit t) b@ is a point paired with a read leg
-- ('Circuit.Equip.UnitCell' is that point), @Poles ch arr a (Unit t)@
-- is a commit paired with a discard.
--
-- Three presentations of one object at the cartesian monomial corner:
--
-- @
-- Cell (,) s (->) i o  ≅  Lens s s o i  ≅  s -> Eval (Mono i o) s
-- @
--
-- named here by 'cellAsLens'\/'lensAsCell' and
-- 'cellAsEval'\/'evalAsCell'.
--
-- == Direction sources
--
-- A 'Cell' at the opposite arrow is a producer: @step@ dualises to
-- @arr ch (t ch a)@, the generalised unfold — an infinite stream at
-- @(,)@, the Elgot settle at @Either@, the cons-list shape at @These@.
-- Running is pairing a consumer cell with a producer cell over the same
-- interface.
--
-- == Gate, not refactor
--
-- The incumbent "Circuit.Machine" and "Circuit.Process" types stand
-- until the sibling-facing migration is priced; the umbrella "Circuit"
-- module does not re-export this one.  'Process' and 'Moore' here
-- shadow the incumbent names by design.
module Circuit.Cell
  ( -- * Two-leg cells
    Cell (..),
    fuse,
    unfuse,

    -- * Polynomial interface
    Machine (..),
    monoMachine,

    -- * Pointing discharges
    Process (..),
    Moore (..),

    -- * Lens bridge
    cellAsLens,
    lensAsCell,

    -- * Eval bridge
    cellAsEval,
    evalAsCell,

    -- * Poles and points
    peek,
    poke,
    polesOf,
    cellOf,
  )
where

import Circuit.Bimonoid (CopyT (..), DiscardT (..))
import Circuit.Body (Body (..))
import Circuit.Category (Category (..), (.>))
import Circuit.Equip (Poles (..), UnitCell (..))
import Circuit.Poly (Dir, Eval (..), Lens, Mono, Poly, Pos, applyLens, lens)
import Circuit.Tensor (Tensor (..), Unit, Unital (..))
import Data.Kind (Type)
import Data.Void (absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Body (Body (..))
-- >>> import Circuit.Equip (Poles (..), UnitCell (..), close)
-- >>> import Circuit.Poly (Dir, Eval (..), Mono, Pos, applyLens)

-- | A stateful cell: an observation and a step, unwired.
--
-- * __@t@ — tick tensor__: how the state is paired with the input on
--   'step''s wire.  @(,)@ is simultaneous sharing; @Either@ and
--   @Data.These.These@ are schedules.  @t@ governs 'step' only — 'obs'
--   has no input to be scheduled against.
-- * __@s@ — state__: the carrier.
-- * __@arr@ — base arrow__: usually @(->)@ or a Kleisli arrow @K m@.
--
-- Moore by construction: 'obs' never consults the input — the Moore
-- condition by type, not by obligation.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> obs c 3
-- 6
-- >>> step c (3, 5)
-- 8
data Cell (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) a b = Cell
  { -- | The observation: read the output from the state alone.
    obs :: arr s b,
    -- | The step: the state paired with the input under the tick tensor
    -- @t@, consumed to write the next state.
    step :: arr (t s a) s
  }

-- | Wire a cell into a 'Body': state and input in together under @t@,
-- state and output out together.
--
-- At @(->)@ this is
--
-- @
-- fuse (Cell o k) = Body (\\(s, a) -> (k (s, a), o s))
-- @
--
-- The state is consulted twice — once by 'step', once by 'obs' — and
-- the constraint is that fact made arrow-level: the input wire must
-- fork ('Circuit.Bimonoid.CopyT' at the input), and reading the state
-- out of the input discards the payload ('Circuit.Bimonoid.DiscardT').
-- On a cartesian base both are free; on a linear or relational one they
-- are not ambient, and neither is fusion.  At @t = Either@ the
-- projection has no arrow — a flowchart tick carries no fusible
-- channel — and the constraint correctly refuses.
--
-- The observation reads the /incoming/ state; a mutant that observed
-- the stepped state would print @(8,16)@ below.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> morphism (fuse c) (3, 5)
-- (8,6)
fuse ::
  forall t s arr a b.
  (CopyT t arr (t s a), DiscardT t arr a) =>
  Cell t s arr a b ->
  Body t s arr a b
fuse (Cell obs step) =
  Body (tensor step (obs . unitr . tensor id (discardT @t)) . copyT)

-- | Unfuse a 'Body' into a cell, at the price of the carrier.
--
-- @
-- unfuse (Body f) = Cell snd (\\((s, _), a) -> f (s, a))
-- @
--
-- A fused body may consult the input when choosing its output — Mealy
-- behaviour — so no cell over the same state can present it.  The
-- carrier grows a slot for the most recent output: 'step' stores the
-- body's whole result, 'obs' reads the slot back.  This is the inside
-- of 'Circuit.Process.bodyToMoore' and 'Circuit.Process.mealy'.
--
-- >>> let adder = Body (\(s, a) -> (s + a, s)) :: Body (,) Int (->) Int Int
-- >>> obs (unfuse adder) (8, 3)
-- 3
-- >>> step (unfuse adder) ((8, 3), 5)
-- (13,8)
--
-- Fused back, the stored output echoes one tick late — the inclusion of
-- Moore in Mealy costs a tick:
--
-- >>> let f = morphism (fuse (unfuse adder))
-- >>> f ((0, 0), 1)
-- ((1,0),0)
-- >>> f ((1, 0), 2)
-- ((3,1),0)
unfuse :: Body (,) s (->) a b -> Cell (,) (s, b) (->) a b
unfuse (Body f) = Cell snd (\((s, _), a) -> f (s, a))

-- | A cell at a polynomial interface @p@: the flat channels become
-- @'Dir' p@ and @'Pos' p@.
--
-- The interface algebra lives here — @Sum@, @Comp@, @PTensor@, the
-- "Circuit.Container" fibres, the Spivak coalgebra layer — because the
-- directions a machine accepts can depend on the position it presents,
-- and @(a, b)@ cannot say that.
--
-- Deliberately unpointed: pointing is the separate discharge the
-- 'Circuit.Equip.UnitCell' taxonomy describes.  The parallel reads —
-- 'Machine' is the polynomial 'Cell', 'Process' is the pointed
-- cartesian-monomial 'Cell' — two different discharges of the same
-- base, not two rungs of one ladder.
--
-- A newtype, not a synonym: 'Dir' and 'Pos' are type families, so GHC
-- cannot invert @Cell t s arr (Dir p) (Pos p)@ to recover @p@.
newtype Machine (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly) = Machine
  { -- | The underlying flat cell, at the interface's direction and
    -- position types.
    machineCell :: Cell t s arr (Dir p) (Pos p)
  }

-- | The monomial corner: a flat cell as a machine at @Mono i o@.
--
-- Absorbs the two encoding taxes the @Mono@ presentation charges: the
-- position is @(o, ())@ and the direction is @Either Void i@.  The
-- successor of 'Circuit.Machine.mooreMono', as a named conversion
-- rather than a smart constructor.
--
-- >>> let m = monoMachine (Cell (*2) (\(s, a) -> s + a)) :: Machine (,) Int (->) (Mono Int Int)
-- >>> case m of Machine cell -> obs cell 3
-- (6,())
-- >>> case m of Machine cell -> step cell (3, Right 5)
-- 8
monoMachine :: Cell (,) s (->) i o -> Machine (,) s (->) (Mono i o)
monoMachine c =
  Machine
    ( Cell
        (\s -> (obs c s, ()))
        (\(s, d) -> case d of Right i -> step c (s, i); Left v -> absurd v)
    )

-- | The seed discharge of a cell: the carrier exposed, the initial
-- state as data.  The cartesian monomial corner, pointed.
--
-- >>> let p = Process 0 (Cell (*2) (\(s, a) -> s + a))
-- >>> (seed p, obs (processCell p) 0)
-- (0,0)
data Process s a b = Process
  { -- | The initial state, as data.
    seed :: s,
    -- | The underlying cell.
    processCell :: Cell (,) s (->) a b
  }

-- | The existential discharge of a cell: the carrier hidden, pointed by
-- injection — the first input creates the initial state.
--
-- Hiding the carrier is what earns composition: a 'Cell' composes only
-- up to carrier product, so it cannot be a 'Category'; with the carrier
-- existential, composition closes.  The instance tower stays on the
-- incumbent 'Circuit.Process.Moore' until the refactor lands.
--
-- The dual fact at the degenerate end: existentially closing
-- 'Circuit.Equip.Poles' collapses to a plain arrow
-- (@∃ch. Poles ch arr a b ≅ arr a b@, co-Yoneda — 'Circuit.Equip.close'
-- is the map, 'Circuit.Equip.copycat' its canonical section).  Closing
-- a cell does not collapse; the hidden-carrier cell is the genuine
-- machine.
--
-- >>> case Moore (+ 1) (Cell (*2) (\(s, a) -> s + a)) of Moore inject cell -> obs cell (inject 10)
-- 22
data Moore a b where
  Moore :: (a -> s) -> Cell (,) s (->) a b -> Moore a b

-- | A cell is an uncurried polynomial lens: @applyLens@ shows a
-- @Lens s s o i@ is @get :: s -> o@ plus @put :: s -> i -> s@ —
-- literally 'obs' and 'step' at @Mono i o@.  This and 'lensAsCell' are
-- field shuffles, which is why 'Circuit.Process.processAsLens' and
-- 'Circuit.Process.lensAsProcess' were one-liners; the bridge belongs
-- next to 'Cell', and moving it is what lets the streaming layer drop
-- its @Poly@ import.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let (o, put) = applyLens (cellAsLens c) 3 in (o, put 5)
-- (6,8)
cellAsLens :: Cell (,) s (->) i o -> Lens s s o i
cellAsLens c = lens (obs c) (\s i -> step c (s, i))

-- | The other shuffle: a lens as a cell.  Round trip:
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let c' = lensAsCell (cellAsLens c) in (obs c' 3, step c' (3, 5))
-- (6,8)
lensAsCell :: Lens s s o i -> Cell (,) s (->) i o
lensAsCell m = Cell (fst . applyLens m) (\(s, i) -> snd (applyLens m s) i)

-- | The third presentation: a cell as a coalgebra
-- @s -> Eval (Mono i o) s@.
--
-- Three presentations of one object — 'Cell', 'Lens', the eval form.
-- With the cell named, the class-mediated conversion
-- ('Circuit.Machine.MachineEval') becomes a statement that the eval
-- form and the two-leg form agree: the coalgebra seat, stated once.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> case cellAsEval c 3 of EP (EK o, EE g) -> (o, g 5)
-- (6,8)
cellAsEval :: Cell (,) s (->) i o -> s -> Eval (Mono i o) s
cellAsEval c s = EP (EK (obs c s), EE (\i -> step c (s, i)))

-- | The eval form as a cell.  Round trip:
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let c' = evalAsCell (cellAsEval c) in (obs c' 3, step c' (3, 5))
-- (6,8)
evalAsCell :: (s -> Eval (Mono i o) s) -> Cell (,) s (->) i o
evalAsCell f =
  Cell
    (\s -> case f s of EP (EK o, _) -> o)
    (\(s, i) -> case f s of EP (_, EE g) -> g i)

-- | The pointed observation: the read leg, precomposed with a point.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let pt = UnitCell (\() -> 3) :: UnitCell (,) (->) Int
-- >>> peek pt c ()
-- 6
peek :: (Category arr) => UnitCell t arr s -> Cell t s arr a b -> arr (Unit t) b
peek pt c = runUnitCell pt .> obs c

-- | The pointed commit: supply the state from a point, then step.
--
-- This is the write leg of a 'Poles' built from a cell — Cell → Poles
-- needs a point, because a pole commits blind (no incoming channel is
-- in scope) and a cell's 'step' expects one.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let pt = UnitCell (\() -> 3) :: UnitCell (,) (->) Int
-- >>> poke pt c 5
-- 8
poke :: (Tensor t arr) => UnitCell t arr s -> Cell t s arr a b -> arr a s
poke pt c = unitl' .> tensor (runUnitCell pt) id .> step c

-- | A machine plus a point is a pair of poles.
--
-- This is the /tight/ grade: poles over the base @arr@, one tick, the
-- channel consumed, nothing copied.  The /loose/ grade — poles over
-- 'Circuit.Body.Body', today's 'Circuit.Machine.machineToPoles' —
-- keeps the channel and hands a copy to the payload, so iteration costs
-- 'Circuit.Bimonoid.Copy': keeping the channel and reading it in the
-- same tick is the fork.  Iteration is composition in the body
-- category; copy is its price of admission.
--
-- >>> let pt = UnitCell (\() -> 3) :: UnitCell (,) (->) Int
-- >>> let m = monoMachine (Cell (*2) (\(s, a) -> s + a))
-- >>> let p = polesOf pt m :: Poles Int (->) (Dir (Mono Int Int)) (Pos (Mono Int Int))
-- >>> conjoint p (Right 5)
-- 8
-- >>> companion p 3
-- (6,())
--
-- The pointed one-shot run is then just a close:
--
-- >>> close (polesOf pt m) (Right 5)
-- (16,())
polesOf ::
  (Tensor t arr) =>
  UnitCell t arr ch ->
  Machine t ch arr p ->
  Poles ch arr (Dir p) (Pos p)
polesOf pt (Machine c) = Poles (poke pt c) (obs c)

-- | The forgetful direction: poles as a cell, by dropping the incoming
-- channel.
--
-- Poles are the memoryless cells — same read leg, a write leg that
-- commits blind.  In Set the Adapter ⊂ Lens inclusion is free (the put
-- ignores the source); here ignoring the channel is a named capability
-- and the sole constraint prices it.  The witness shows the channel
-- being forgotten: @99@ is discarded, not consulted.
--
-- >>> let pl = Poles (* 10) (+ 1) :: Poles Int (->) Int Int
-- >>> let cpl = cellOf pl :: Cell (,) Int (->) Int Int
-- >>> step cpl (99, 5)
-- 50
-- >>> obs cpl 7
-- 8
cellOf ::
  forall t ch arr a b.
  (DiscardT t arr ch) =>
  Poles ch arr a b ->
  Cell t ch arr a b
cellOf (Poles commit observe) =
  Cell observe (tensor (discardT @t) id .> unitl .> commit)

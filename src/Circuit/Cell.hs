{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A state machine as two unwired legs — an observation and a step —
-- and the grid of types around it.
--
-- @
-- data Cell t s arr a b = Cell
--   { observe :: arr s b,
--     step    :: arr (t s a) s
--   }
-- @
--
-- The parts inventory: a state machine contains a step and an extract.
-- What a fused representation adds is a wiring decision — that the two
-- legs share one input wire and one tick.  'Cell' is the inventory as
-- data; 'Body' is the same machine with the wiring soldered.
--
-- == The grid
--
-- @
--                          flat (a, b)    polynomial p
-- unfused, unpointed       Cell           Machine
-- fused,   unpointed       Body           Body at (Dir p, Pos p) — needs no name
-- unfused, seed as data    Process        —   (not here yet)
-- unfused, hidden carrier  Moore          —   (not here yet)
-- carrier in the trace     —              Closed
-- @
--
-- Fused\/unfused is the Mealy\/Moore axis, disposed of without a
-- parameter: 'Body' permits the emit leg to read the input; 'Cell'
-- structurally forbids it.  A tick index would be one shape at two
-- settings; this is two types, and the translations between them —
-- 'fuse' total but copy-gated, 'unfuse' total but carrier-changing —
-- are the content of the distinction, visible in the signatures.
--
-- What each earns:
--
-- * 'Cell' — the coalgebra.  Constructible at any @t@\/@arr@ with no
--   copy capability.  What runners consume.
-- * 'Body' — the traced-monoidal citizen: @yank@ needs the fused shape,
--   so Body survives rather than becoming derived-only.
-- * 'Machine' — where the interface algebra lives: @Sum@, @Comp@,
--   @PTensor@, the "Circuit.Container" fibres, the Spivak coalgebra
--   layer.
-- * @Process@ — the seed discharge (not in this module yet).
-- * @Moore@ — the existential discharge: hiding the carrier is what
--   makes composition close (not in this module yet).
--
-- 'Cell' itself gets no instances: it is a data shape with conversions.
-- The payoff is representational honesty — the fuse\/unfuse asymmetry
-- and the optic grading below becoming visible — not new capability.
--
-- == The optic grading
--
-- @
-- Poles ch arr a b    = (commit :: arr a ch,        observe :: arr ch b)
-- Cell   t ch arr a b = (step   :: arr (t ch a) ch, observe :: arr ch b)
-- @
--
-- Same read leg; the write legs differ by exactly whether the incoming
-- channel is in scope.  The shared 'observe' field name makes that
-- visible at every use site (and costs 'DuplicateRecordFields').  In
-- optic language, 'Poles' is an Adapter (no @t@ parameter — profunctor
-- structure suffices), 'Cell' is a Lens (the tensor is needed because
-- 'step' holds the source alongside the focus), and 'Body' at
-- @(,)@\/@(->)@ is the State-Kleisli image,
-- @(ch, a) -> (ch, b) ≅ a -> State ch b@.  'fuse' is the textbook
-- lens-to-stateful-action conversion, and its copy requirement is the
-- categorical content of why that conversion is not free outside a
-- cartesian base.  In Set the Adapter ⊂ Lens inclusion is free; here
-- forgetting the channel is a capability, priced as a 'Cap'.
--
-- 'Point' and 'Cap' are the boundary cases: @Poles ch arr (Unit t) b@
-- is a point paired with a read leg, @Poles ch arr a (Unit t)@ is a
-- commit paired with a cap.
--
-- == Three presentations of one object
--
-- At the cartesian monomial corner:
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
-- A 'Cell' at the opposite arrow is a producer: 'step' dualises to
-- @arr ch (t ch a)@, the generalised unfold — an infinite stream at
-- @(,)@, the Elgot settle at @Either@, the cons-list shape at @These@.
-- Running is pairing a consumer cell with a producer cell over the same
-- interface.
--
-- == Candidate replacement
--
-- This module is the candidate spine, not a refactor: the incumbent
-- "Circuit.Body", "Circuit.Equip", "Circuit.Machine" and
-- "Circuit.Process" modules stand untouched, nothing outside this file
-- is kept or removed yet, and the umbrella "Circuit" module does not
-- re-export this one.  Names shared with incumbents ('Body', 'Poles',
-- 'close', 'copycat') are the candidate spellings; @commit@ also
-- collides with the field of 'Circuit.Equip.In' and @observe@ with
-- "Circuit.Hyper" — both collisions are accepted for the candidate.
module Circuit.Cell
  ( -- * Two-leg cells
    Cell (..),

    -- * The fused span
    Body (..),

    -- * Wiring moves
    fuse,
    unfuse,

    -- * Polynomial interface
    Machine (..),
    monoMachine,

    -- * Poles, points, caps
    Poles (..),
    Point (..),
    Cap (..),
    capT,
    close,
    copycat,

    -- * Pointed eliminators
    peek,
    poke,
    polesOf,
    cellOf,

    -- * Lens bridge
    cellAsLens,
    lensAsCell,

    -- * Eval bridge
    cellAsEval,
    evalAsCell,
  )
where

import Circuit.Bimonoid (CopyT (..), Discard (..), DiscardT (..))
import Circuit.Category (Category (..), (.>))
import Circuit.Poly (Dir, Eval (..), Lens, Mono, Poly, Pos, applyLens, lens)
import Circuit.Tensor (Tensor (..), Unit, Unital (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Poly (Dir, Eval (..), Mono, Pos, applyLens)

-- | A stateful cell: an observation and a step, unwired.
--
-- * __@t@ — tick tensor__: how the state is paired with the input on
--   'step''s wire.  @(,)@ is simultaneous sharing; @Either@ and
--   @Data.These.These@ are schedules.  @t@ governs 'step' only —
--   'observe' has no input to be scheduled against.
-- * __@s@ — state__: the carrier.
-- * __@arr@ — base arrow__: usually @(->)@ or a Kleisli arrow @K m@.
--
-- Moore by construction: 'observe' never consults the input — the
-- Moore condition by type, not by obligation.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> case c of Cell o _ -> o 3
-- 6
-- >>> case c of Cell _ k -> k (3, 5)
-- 8
data Cell (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) a b = Cell
  { -- | The observation: read the output from the state alone.
    observe :: arr s b,
    -- | The step: the state paired with the input under the tick tensor
    -- @t@, consumed to write the next state.
    step :: arr (t s a) s
  }

-- | A morphism across a tensored channel: the fused span.
--
-- @
-- Body t ch arr a b  =  arr (t ch a) (t ch b)
-- @
--
-- Channel and payload enter together and exit together — the wiring
-- 'Cell' leaves undecided, soldered.  The Mealy shape: the emit leg
-- may consult the input.  This is the traced-monoidal citizen —
-- @yank@ needs the fused span — and a 'Category' by plain composition:
-- composition in this category is the threading.
--
-- >>> let b = Body (\(s, a) -> (s + a, s * 2)) :: Body (,) Int (->) Int Int
-- >>> morphism b (3, 5)
-- (8,6)
newtype Body t ch arr a b = Body {morphism :: arr (t ch a) (t ch b)}

instance (Category arr) => Category (Body t ch arr) where
  id :: forall a. Body t ch arr a a
  id = Body id
  {-# INLINE id #-}

  (.) :: forall a b c. Body t ch arr b c -> Body t ch arr a b -> Body t ch arr a c
  Body g . Body f = Body (g . f)
  {-# INLINE (.) #-}

-- | Wire a cell into a 'Body': state and input in together under @t@,
-- state and output out together.
--
-- At @(->)@ this is
--
-- @
-- fuse (Cell o k) = Body (\\(s, a) -> (k (s, a), o s))
-- @
--
-- The state is consulted twice — once by 'step', once by 'observe' —
-- and the constraint is that fact made arrow-level: the input wire
-- must fork ('Circuit.Bimonoid.CopyT' at the input), and reading the
-- state out of the input discards the payload
-- ('Circuit.Bimonoid.DiscardT').  On a cartesian base both are free;
-- on a linear or relational one they are not ambient, and neither is
-- fusion.  At @t = Either@ the projection has no arrow — a flowchart
-- tick carries no fusible channel — and the constraint correctly
-- refuses.
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
fuse (Cell o k) =
  Body (tensor k (o . unitr . tensor id (discardT @t)) . copyT)

-- | Unfuse a 'Body' into a cell, at the price of the carrier.
--
-- A fused body may consult the input when choosing its output — Mealy
-- behaviour — so no cell over the same state can present it.  The
-- carrier grows a slot for the most recent output: 'step' stores the
-- body's whole result, 'observe' reads the slot back.  The
-- enlargement is a cartesian pair, so @t@ is @(,)@ on the nose — the
-- shape of the move, not a chosen specialization — while @arr@ stays
-- general, and the two 'Circuit.Bimonoid.Discard' constraints are the
-- price of the slot's droppable wires.
--
-- >>> let adder = Body (\(s, a) -> (s + a, s)) :: Body (,) Int (->) Int Int
-- >>> case unfuse adder of Cell o _ -> o (8, 3)
-- 3
-- >>> case unfuse adder of Cell _ k -> k ((8, 3), 5)
-- (13,8)
--
-- Fused back, the stored output echoes one tick late — the inclusion
-- of Moore in Mealy costs a tick:
--
-- >>> let f = morphism (fuse (unfuse adder))
-- >>> f ((0, 0), 1)
-- ((1,0),0)
-- >>> f ((1, 0), 2)
-- ((3,1),0)
unfuse ::
  forall s arr a b.
  (Tensor (,) arr, Discard arr s, Discard arr b) =>
  Body (,) s arr a b ->
  Cell (,) (s, b) arr a b
unfuse (Body f) = Cell projSnd (tensor projFst id .> f)
  where
    projFst :: arr (s, b) s
    projFst = unitr . tensor id discard
    projSnd :: arr (s, b) b
    projSnd = unitl . tensor discard id

-- | A cell at a polynomial interface @p@: the flat channels become
-- @'Dir' p@ and @'Pos' p@.
--
-- The interface algebra lives here — @Sum@, @Comp@, @PTensor@, the
-- "Circuit.Container" fibres, the Spivak coalgebra layer — because the
-- directions a machine accepts can depend on the position it presents,
-- and @(a, b)@ cannot say that.
--
-- Deliberately unpointed: pointing is the separate discharge of the
-- pointing taxonomy.  The parallel reads — 'Machine' is the polynomial
-- 'Cell', and the seed-as-data discharge is the pointed
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
-- The two encoding taxes of the @Mono@ presentation, paid with
-- unitors: the position is @(o, ())@ — the cartesian right unitor —
-- and the direction is @Either Void i@ — the coproduct left unitor,
-- @Unit Either = Void@.  No @absurd@ at the value level; the Void
-- elimination is the unitor.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let m = monoMachine c :: Machine (,) Int (->) (Mono Int Int)
-- >>> case m of Machine (Cell o _) -> o 3
-- (6,())
-- >>> case m of Machine (Cell _ k) -> k (3, Right 5)
-- 8
monoMachine ::
  (Tensor t arr, Unital (,) arr, Unital Either arr) =>
  Cell t s arr i o ->
  Machine t s arr (Mono i o)
monoMachine (Cell o k) =
  Machine (Cell (o .> unitr') (tensor id unitl .> k))

-- | A matched pair of channel poles: a write leg and a read leg over a
-- shared carrier and base.
--
-- @
-- Poles ch arr a b = (commit :: arr a ch, observe :: arr ch b)
-- @
--
-- The memoryless cell: same read leg, but the write leg commits
-- blind — the incoming channel is not in scope.  In optic language,
-- 'Poles' is the Adapter to 'Cell''s Lens: no @t@ parameter, because
-- profunctor structure suffices; the tensor is needed exactly when the
-- source must be held alongside the focus.
data Poles ch arr a b = Poles
  { -- | Write leg: commit the payload to the channel, blind to the
    -- incoming channel.
    commit :: arr a ch,
    -- | Read leg: observe the channel.  The same shape — and the same
    -- name — as 'Cell''s read leg.
    observe :: arr ch b
  }

-- | A point of the carrier: an arrow out of the tensor unit.
--
-- The left-degenerate pole: @Poles ch arr (Unit t) b@ is a 'Point'
-- paired with a read leg.  The incumbent spelling is
-- 'Circuit.Equip.UnitCell'.
newtype Point t arr ch = Point
  { runPoint :: arr (Unit t) ch
  }

-- | A cap of the carrier: an arrow into the tensor unit — the discard,
-- as data.
--
-- The right-degenerate pole: @Poles ch arr a (Unit t)@ is a commit
-- paired with a 'Cap'.
newtype Cap t arr ch = Cap
  { runCap :: arr ch (Unit t)
  }

-- | The discard capability, as a value.
--
-- >>> runCap (capT :: Cap (,) (->) Int) 4
-- ()
capT :: forall t arr ch. (DiscardT t arr ch) => Cap t arr ch
capT = Cap (discardT @t)

-- | Close a same-carrier pole by composing its legs.  This is the
-- co-Yoneda map @∃ch. Poles ch arr a b ≅ arr a b@; 'copycat' is its
-- canonical section, and @close copycat = id@ is the round trip.
--
-- >>> close (Poles (* 2) (+ 1)) 3
-- 7
close :: (Category arr) => Poles ch arr a b -> arr a b
close (Poles c o) = c .> o

-- | The copycat strategy: identity legs at any carrier.
--
-- >>> close (copycat :: Poles Int (->) Int Int) 4
-- 4
copycat :: (Category arr) => Poles ch arr ch ch
copycat = Poles id id

-- | The pointed observation: the read leg, precomposed with a point.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let pt = Point (\() -> 3) :: Point (,) (->) Int
-- >>> peek pt c ()
-- 6
peek :: (Category arr) => Point t arr s -> Cell t s arr a b -> arr (Unit t) b
peek pt (Cell o _) = runPoint pt .> o

-- | The pointed commit: supply the state from a point, then step.
--
-- This is the write leg of a 'Poles' built from a cell — Cell → Poles
-- needs a point, because a pole commits blind (no incoming channel is
-- in scope) and a cell's 'step' expects one.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let pt = Point (\() -> 3) :: Point (,) (->) Int
-- >>> poke pt c 5
-- 8
poke :: (Tensor t arr) => Point t arr s -> Cell t s arr a b -> arr a s
poke pt (Cell _ k) = unitl' .> tensor (runPoint pt) id .> k

-- | A machine plus a point is a pair of poles.
--
-- This is the /tight/ grade: poles over the base @arr@ — one tick, the
-- channel consumed, nothing copied.  The /loose/ grade, poles over
-- 'Body', keeps the channel and hands a copy to the payload, so
-- iteration costs 'Circuit.Bimonoid.Copy': keeping the channel and
-- reading it in the same tick is the fork.  Iteration is composition
-- in the body category; copy is its price of admission.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let pt = Point (\() -> 3) :: Point (,) (->) Int
-- >>> let m = monoMachine c
-- >>> let p = polesOf pt m :: Poles Int (->) (Dir (Mono Int Int)) (Pos (Mono Int Int))
-- >>> commit p (Right 5)
-- 8
-- >>> case p of Poles _ o -> o 3
-- (6,())
--
-- The pointed one-shot run is then just a close:
--
-- >>> close (polesOf pt m) (Right 5)
-- (16,())
polesOf ::
  (Tensor t arr) =>
  Point t arr ch ->
  Machine t ch arr p ->
  Poles ch arr (Dir p) (Pos p)
polesOf pt (Machine c@(Cell o _)) = Poles (poke pt c) o

-- | The forgetful direction: poles as a cell, by dropping the incoming
-- channel.
--
-- In Set this inclusion is free; here it costs a 'Cap' — the discard,
-- as data.  The witness shows the channel being forgotten: @99@ is
-- discarded, not consulted.
--
-- >>> let pl = Poles (* 10) (+ 1) :: Poles Int (->) Int Int
-- >>> let cpl = cellOf (capT :: Cap (,) (->) Int) pl
-- >>> step cpl (99, 5)
-- 50
-- >>> case cpl of Cell o _ -> o 7
-- 8
cellOf :: (Tensor t arr) => Cap t arr ch -> Poles ch arr a b -> Cell t ch arr a b
cellOf (Cap cap) (Poles w r) =
  Cell r (tensor cap id .> unitl .> w)

-- | A cell is an uncurried polynomial lens: @applyLens@ shows a
-- @Lens s s o i@ is @get :: s -> o@ plus @put :: s -> i -> s@ —
-- literally 'observe' and 'step' at @Mono i o@.  This and 'lensAsCell'
-- are field shuffles; the corner specialization is the content, since
-- 'Lens' is a function-space type.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> let (o, put) = applyLens (cellAsLens c) 3 in (o, put 5)
-- (6,8)
cellAsLens :: Cell (,) s (->) i o -> Lens s s o i
cellAsLens (Cell o k) = lens o (curry k)

-- | The other shuffle: a lens as a cell.  Round trip:
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> case lensAsCell (cellAsLens c) of Cell o k -> (o 3, k (3, 5))
-- (6,8)
lensAsCell :: Lens s s o i -> Cell (,) s (->) i o
lensAsCell m = Cell (fst . applyLens m) (\(s, i) -> snd (applyLens m s) i)

-- | The third presentation: a cell as a coalgebra
-- @s -> Eval (Mono i o) s@.  With the cell named, the class-mediated
-- conversion becomes a statement that the eval form and the two-leg
-- form agree — the coalgebra seat, stated once.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> case cellAsEval c 3 of EP (EK o, EE g) -> (o, g 5)
-- (6,8)
cellAsEval :: Cell (,) s (->) i o -> s -> Eval (Mono i o) s
cellAsEval (Cell o k) s = EP (EK (o s), EE (\i -> k (s, i)))

-- | The eval form as a cell.  Round trip:
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> case evalAsCell (cellAsEval c) of Cell o k -> (o 3, k (3, 5))
-- (6,8)
evalAsCell :: (s -> Eval (Mono i o) s) -> Cell (,) s (->) i o
evalAsCell f =
  Cell
    (\s -> case f s of EP (EK o, _) -> o)
    (\(s, i) -> case f s of EP (_, EE g) -> g i)

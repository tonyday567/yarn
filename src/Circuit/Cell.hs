{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

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
-- carrier in the trace     —              Closed          (not here yet)
-- @
--
-- 'Circuit.Machine.Closed' is @Trace t arr (Dir p) (Pos p)@, and on
-- this spine it is downstream of 'fuse': the trace needs the fused
-- span, so a cell arrives there by @yank . fuse@ — copy-gated, not a
-- peer of the unfused rows.
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
-- * The run — 'closedToGenerator' (@fuse@ plus a unitor, copy-priced)
--   and 'Unfold' (the generator settled to its behaviour): build a
--   machine, close it against a source, take its stream finitely.
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
-- visible at the types (costing 'DuplicateRecordFields'; with
-- 'OverloadedRecordDot' the selectors read @c.observe@ regardless).  In
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
-- A 'Cell' at the opposite arrow is a producer — a 'Cocell':
--
-- @
-- type Cocell t ch arr a b = Cell t ch (Op arr) a b
--   observe :: Op arr ch b        =  arr b ch         -- commit leg
--   step    :: Op arr (t ch a) ch =  arr ch (t ch a)  -- emit leg
-- @
--
-- Both legs are per-tick.  The commit leg positions a channel from a
-- payload — degenerate for a constant stream (@const ()@: positioned
-- from nowhere), real for a resumable one (@\\n -> n@: start emitting
-- from n).  The emit leg is the generalised unfold: an infinite stream
-- at @(,)@, the Elgot settle at @Either@, the cons-list shape at
-- @These@.  Neither leg says "once, at the start" — initialisation is
-- not a leg of anything; it is a 'Point', applied to the closed cell,
-- once, from outside.
--
-- 'Cocell' is a synonym, not a newtype: the field selectors are the
-- point — @step@ on a cocell is still 'step'.  (The codata name would
-- belong to the fixed point, @Nu t arr b@; a cocell is the generator
-- that unfolds into it.)  The Op-side spellings stay prose —
-- @runOp . observe@ is the commit leg, @runOp . step@ the emit leg;
-- @commit@ is already 'Poles'' field name in this module.
--
-- 'pair' closes a producer and a consumer over the same interface.
-- The unbounded run is packaged now too: 'closedToGenerator' (fuse
-- plus a unitor, costing copy) turns the closed cell into a
-- generator, and 'Unfold' settles the generator to its behaviour —
-- the counter doctest there takes the stream finitely.
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
    unclose,
    copycat,

    -- * Pointed eliminators
    peek,
    poke,
    polesOf,
    cellOf,

    -- * Direction sources
    Cocell,
    cocell,
    pair,

    -- * The run
    closedToGenerator,
    Unfold (..),

    -- * Lens bridge
    cellAsLens,
    lensAsCell,

    -- * Eval bridge
    cellAsEval,
    evalAsCell,
  )
where

import Circuit.Bimonoid (CopyT (..), Discard (..), DiscardT (..))
import Circuit.Category (Category (..), Op (..), (.>))
import Circuit.Poly (Dir, Eval (..), Lens, Mono, Poly, Pos, applyLens, lens)
import Circuit.Tensor (Action (..), Tensor (..), Unit, Unital (..))
import Circuit.Traced (Assoc (..), Yank (..))
import Data.Kind (Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XOverloadedRecordDot
-- >>> import Circuit.Category (Op (..))
-- >>> import Circuit.Poly (Dir, Eval (..), Mono, Pos, applyLens)
-- >>> import Circuit.Traced (yank)
-- >>> import Data.These (These (..))

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
-- >>> c.observe 3
-- 6
-- >>> c.step (3, 5)
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
-- ('Circuit.Bimonoid.DiscardT').  One precision: the copy is taken at
-- the whole input wire, so at a linear base the payload must be
-- copyable, not just the state.  The minimal statement of the
-- requirement is a copy at the state alone — the state is what is
-- consulted twice; this routing takes the bigger copy in exchange for
-- avoiding an associator and a braiding step.  On a cartesian base
-- both are free; on a linear or relational one they are not ambient,
-- and neither is fusion.  At @t = Either@ the projection has no
-- arrow — a flowchart tick carries no fusible channel — and the
-- constraint correctly refuses.
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
-- >>> (unfuse adder).observe (8, 3)
-- 3
-- >>> (unfuse adder).step ((8, 3), 5)
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
-- >>> m.machineCell.observe 3
-- (6,())
-- >>> m.machineCell.step (3, Right 5)
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
--
-- As a fact about the consumer direction, 'Poles' is 'Cell' at a
-- channel-forgetting tensor: with @Const ch a = a@,
-- @commit :: arr (Const ch a) ch = arr a ch@.  Sharper at the fused
-- grade: @Body Const ch arr a b = arr (Const ch a) (Const ch b) =
-- arr a b@ — the fused span at the second projection is the base
-- arrow, which is why 'Poles' needs no @t@: its fused form has
-- already left the channel behind.
--
-- But the projection runs out exactly where 'Cell''s @t@ works.  It is
-- left-unital
-- only — @Const (Unit t) a = a@ holds, but @Const a (Unit t) = Unit t@ —
-- so 'Unital' is uninhabitable there and 'fuse' cannot be instantiated
-- at all: 'close' and 'fuse' are parallel moves at two grades, not one
-- function at two instantiations.  The producer direction also dies
-- under it — a 'Cocell' step @arr ch (Const ch a)@ returns no channel.
-- So the fact stays a haddock line and 'Poles' stays its own type.
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

-- | Close a same-carrier pole by composing its legs: a component, at
-- this carrier, of the co-Yoneda map @∃ch. Poles ch arr a b ≅ arr a b@.
-- The existential closure of a pole is the base arrow — closing a
-- 'Poles' loses everything, which is why the library closes squares
-- into 'Circuit.Equip.TwoCell' and never closes poles.
--
-- >>> close (Poles (* 2) (+ 1)) 3
-- 7
close :: (Category arr) => Poles ch arr a b -> arr a b
close (Poles c o) = c .> o

-- | The section of 'close': a plain arrow as a pole whose carrier is
-- its own output type, with an identity read leg.  The round trip is
-- @close . unclose = id@; the other direction, @unclose . close@, is
-- not the identity — it moves the carrier from @ch@ to @b@.  Same
-- asymmetry as 'fuse'\/'unfuse', one grade down: total in both
-- directions, carrier-changing on the return.
--
-- >>> close (unclose (+ 1)) 3
-- 4
unclose :: (Category arr) => arr a b -> Poles b arr a b
unclose f = Poles f id

-- | The copycat strategy: identity legs at any carrier —
-- @unclose id@, and @close copycat = id@ is the round trip's special
-- case.
--
-- >>> close (copycat :: Poles Int (->) Int Int) 4
-- 4
copycat :: (Category arr) => Poles ch arr ch ch
copycat = unclose id

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
-- >>> p.commit (Right 5)
-- 8
-- >>> p.observe 3
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
-- >>> cpl.step (99, 5)
-- 50
-- >>> cpl.observe 7
-- 8
cellOf :: (Tensor t arr) => Cap t arr ch -> Poles ch arr a b -> Cell t ch arr a b
cellOf (Cap cap) (Poles w r) =
  Cell r (tensor cap id .> unitl .> w)

-- * Direction sources

-- | A producer cell: a 'Cell' at the opposite arrow.
--
-- The synonym is the point — 'step' on a cocell is still 'step'.  The
-- emit leg @arr ch (t ch a)@ is the generalised unfold: an infinite
-- stream at @(,)@, the Elgot settle at @Either@, the cons-list shape
-- at @These@.  The commit leg @arr b ch@ positions a channel from a
-- payload: degenerate for a constant stream, real for a resumable one.
type Cocell t ch arr a b = Cell t ch (Op arr) a b

-- | Build a cocell from its two legs, without the 'Op' wrappers.
--
-- >>> let ones = cocell (const ()) (\() -> ((), 1)) :: Cocell (,) () (->) Int ()
-- >>> runOp (ones.step) ()
-- ((),1)
-- >>> runOp (ones.observe) ()
-- ()
cocell :: arr b ch -> arr ch (t ch a) -> Cocell t ch arr a b
cocell o s = Cell (Op o) (Op s)

-- | Pair a producer with a consumer over the same interface: the
-- producer's emit leg supplies the consumer's input each tick, and the
-- producer's channel is discarded at the read leg.
--
-- @
-- step:    t (t chP chC) (Unit t)
--            --unitr------------\> t chP chC
--            --emit g ⊗ id------\> t (t chP a) chC
--            --assoc------------\> t chP (t a chC)
--            --id ⊗ braid-------\> t chP (t chC a)
--            --id ⊗ step c------\> t chP chC
-- observe: t chP chC
--            --cap ⊗ observe c--\> t (Unit t) b
--            --unitl------------\> b
-- @
--
-- Linear in both channels: no 'Circuit.Bimonoid.CopyT' anywhere — the
-- only capabilities are the producer-channel discard and the tensor's
-- symmetry (the producer's output and the consumer's channel arrive
-- out of order after @assoc@, and 'braid' swaps them; at a
-- non-symmetric tensor the pairing honestly refuses).  The producer's
-- commit leg is not consumed by pairing; it is structure the type
-- carries, available for splicing or restarting producers — 'Poles''
-- legs are not all used by 'close' either.
--
-- >>> let counter = Cell id (\(ch, a) -> ch + a) :: Cell (,) Int (->) Int Int
-- >>> let ones = cocell (const ()) (\() -> ((), 1)) :: Cocell (,) () (->) Int ()
-- >>> let closed = pair ones counter
-- >>> closed.observe ((), 3)
-- 3
-- >>> closed.step (((), 3), ())
-- ((),4)
--
-- An order-sensitive consumer pins the braid (a braid-dropped mutant
-- would print @((),-2)@):
--
-- >>> let down = Cell id (\(ch, a) -> ch - a) :: Cell (,) Int (->) Int Int
-- >>> (pair ones down).step (((), 3), ())
-- ((),2)
--
-- Two ticks by hand: 'observe' and 'step' alternated by the caller is
-- the run — pre-step readings, the ε-output included:
--
-- >>> let ch1 = closed.step (((), 0), ()); ch2 = closed.step (ch1, ()) in (closed.observe ((), 0), closed.observe ch1, closed.observe ch2)
-- (0,1,2)
pair ::
  forall t chP chC arr a x b.
  (Action t arr, Assoc t arr, DiscardT t arr chP) =>
  Cocell t chP arr a x ->
  Cell t chC arr a b ->
  Cell t (t chP chC) arr (Unit t) b
pair (Cell _ pk) (Cell o k) = Cell observeP stepP
  where
    observeP :: arr (t chP chC) b
    observeP = tensor (discardT @t) o .> unitl
    stepP :: arr (t (t chP chC) (Unit t)) (t chP chC)
    stepP = unitr .> tensor (runOp pk) idC .> assoc .> tensor idP (braid .> k)
    idP :: arr chP chP
    idP = id
    idC :: arr chC chC
    idC = id

-- * The run

-- | The closed cell as a generator: 'fuse' plus the right unitor.
--
-- @
-- fuse c          :: Body t ch arr (Unit t) b = arr (t ch (Unit t)) (t ch b)
-- closedToGenerator c = unitr' .> morphism (fuse c)
-- @
--
-- The price is 'fuse''s — a copy at the whole input wire and a
-- discard of the unit payload, both constraints inherited from it.
-- What 'pair' produces, this runs: the producer/consumer/closed
-- family is closed under generation.
--
-- The counter, finished — built, closed against a source, and taken
-- finitely:
--
-- >>> let counter = Cell id (\(ch, a) -> ch + a) :: Cell (,) Int (->) Int Int
-- >>> let ones = cocell (const ()) (\() -> ((), 1)) :: Cocell (,) () (->) Int ()
-- >>> take 4 (unfold (closedToGenerator (pair ones counter)) ((), 0))
-- [0,1,2,3]
closedToGenerator ::
  forall t ch arr b.
  (CopyT t arr (t ch (Unit t)), DiscardT t arr (Unit t)) =>
  Cell t ch arr (Unit t) b ->
  arr ch (t ch b)
closedToGenerator c = unitr' .> morphism (fuse c)

-- | Iteration as a capability, added like 'Yank': not derivable from
-- finite structure. A generator @arr ch (t ch b)@ steps its channel
-- under @t@, emitting a @b@ each tick; 'unfold' settles it to the
-- behaviour type @Nu t arr b@. Where 'yank' closes the feedback loop,
-- 'unfold' refuses it — the channel runs forward forever, and the
-- base arrow decides what shape the forever takes:
--
-- @
-- Nu (,)   (->) b = [b]   — the stream
-- Nu Either (->) b = b    — the settle
-- Nu These  (->) b = [b]  — the scheduled list, nil reachable
-- @
--
-- 'Nu' at @(,)@ lands on the list deliberately: the library's stream
-- carrier already is @[b]@ — "Circuit.Stream"'s 'Uncons'/'Cons'/'Snoc'
-- classes are instantiated at @[]@, and the lazy-knot witnesses in
-- "Circuit.Traced" return lists. A dedicated stream type would wrap
-- exactly the laziness Haskell lists already have, and 'Nu' is the
-- type every runner's output will mention.
--
-- The relationship to 'Yank' is per-tensor, and all three rows are
-- pinned:
--
-- * 'Either' — interderivable: the same capability at two
--   presentations. Forward: @unfold g = yank (either g g)@, the
--   codiagonal pairing the two entry points. Reverse:
--   @yank f = unfold (either (Left . Left) Right . f) . Right@ —
--   the generator state is the yank state, and @Left . Left@ feeds
--   a 'Left' result back in as the next state. For all @f@ both
--   sides apply @f@ to the same sequence of states and agree on the
--   result: induction on the number of 'Left' steps, with both
--   sides diverging together when no 'Right' is ever produced. The
--   doctests below witness both directions at a point; the
--   quantified argument is two lines of prose, not an oracle.
-- * 'These' — 'Yank' is derivable from 'Unfold', not conversely:
--   @yank f = head . unfold g . That@ where @g@ reschedules a body
--   'This' on the reconstructed state and maps both exit branches to
--   a generator 'That', making the stream a singleton by
--   construction. The converse cannot hold — a single settled value
--   cannot carry a stream — so 'Unfold' at 'These' is the strictly
--   stronger half, and the first 'These'-indexed capability in the
--   library with iteration semantics. See the instance below for
--   the witness.
-- * @(,)@ — incomparable. The 'Yank' @(,)@ instance ties a lazy
--   knot: self-reference, no seed, one value. 'unfold' runs a seed
--   forward: iteration, a stream. A knot is not an iteration, and a
--   stream is not a fixed point; neither derives from the other.
--
-- The class takes no 'Yank' superclass: the only row where the two
-- coincide needs no extra structure to say so.
--
-- One consequence of the table, logged: @Nu (,) (->) b@ and
-- @Nu These (->) b@ are the same type at different termination — the
-- @(,)@ stream is always infinite, the 'These' list may end. A
-- runner polymorphic in @t@ sees @[b]@ either way and cannot read
-- termination off the type; the tensor's promise is discarded at
-- the boundary. The list decision stands, but the sharpest argument
-- for ever introducing a dedicated stream type is type-level
-- termination, not laziness.
class
  (Category arr) =>
  Unfold (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  -- | The behaviour type: what running a generator forever settles to.
  type Nu t arr b

  -- | Settle a generator to its behaviour.
  unfold :: arr ch (t ch b) -> arr ch (Nu t arr b)

-- | Cartesian: the stream. Laziness is the point — the lazy @(:)@
-- puts each element in front of the next channel step, so a
-- productive generator yields an infinite list.
--
-- >>> take 4 (unfold (\ch -> (ch + 1, ch)) (0 :: Int))
-- [0,1,2,3]
instance Unfold (,) (->) where
  type Nu (,) (->) b = [b]
  unfold g = go
    where
      go ch = case g ch of (ch', b) -> b : go ch'

-- | Cocartesian: the settle. @Nu Either (->) b = b@ — the generator
-- iterates to its 'Right' and hands over the payload. Forward half
-- of the interderivability with 'Yank': @unfold g = yank (either g
-- g)@, so the instance delegates to 'yank' through the codiagonal
-- rather than duplicating the loop.
--
-- >>> let down n = if n <= (0 :: Int) then Right n else Left (n - 1)
-- >>> unfold down 5
-- 0
-- >>> unfold down 5 == yank (either down down) 5
-- True
-- >>> let body n = (case either id id n of { m | m > 0 -> Left (m - 1); m -> Right m }) :: Either Int Int
-- >>> yank body 5
-- 0
-- >>> (unfold (either (Left . Left) Right . body) . Right) 5
-- 0
instance Unfold Either (->) where
  type Nu Either (->) b = b
  unfold g = yank (either g g)

-- | Inclusive: the scheduled list. 'This' reschedules without
-- emitting, 'These' is the cons cell — emit and continue — and
-- 'That' is the nil: halt with the final payload. The list may end,
-- unlike the @(,)@ stream. The generator reads 'These' as
-- produce-and-reschedule, where the body of 'Yank' 'These' reads the
-- same constructor as exit (@These _ c -> c@). The conventions
-- differ, and the derivation shows which way the strength runs:
-- @yank f = head . unfold g . That@ with @g@ rescheduling a body
-- 'This' on the reconstructed state and mapping both exit branches
-- to a generator 'That' — the settled payload is the singleton
-- stream's head. Witnessed at a point:
--
-- >>> let body x = (case x of That n | n > 0 -> This (n - 1); That n -> That n; This s -> These (s + 1) (s * 10)) :: These Int Int
-- >>> yank body (3 :: Int)
-- 20
-- >>> let gen x = case body x of This s -> This (This s); That c -> That c; These _ c -> That c
-- >>> unfold gen (That 3)
-- [20]
--
-- >>> let ticks ch = if ch <= (0 :: Int) then That ch else These (ch - 1) ch
-- >>> unfold ticks 3
-- [3,2,1,0]
instance Unfold These (->) where
  type Nu These (->) b = [b]
  unfold g = go
    where
      go ch = case g ch of
        This ch' -> go ch'
        That b -> [b]
        These ch' b -> b : go ch'

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
-- >>> let c' = lensAsCell (cellAsLens c) in (c'.observe 3, c'.step (3, 5))
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
-- >>> let c' = evalAsCell (cellAsEval c) in (c'.observe 3, c'.step (3, 5))
-- (6,8)
evalAsCell :: (s -> Eval (Mono i o) s) -> Cell (,) s (->) i o
evalAsCell f =
  Cell
    (\s -> case f s of EP (EK o, _) -> o)
    (\(s, i) -> case f s of EP (_, EE g) -> g i)

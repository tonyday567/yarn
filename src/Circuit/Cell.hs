{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | An unfused 'Circuit.Body.Body': a stateful computation as two legs,
-- with the wiring between them undecided.
--
-- @
-- data Cell t s arr a b = Cell
--   { peek :: arr s b,
--     poke :: arr (t s a) s
--   }
-- @
--
-- The parts inventory: a state machine contains an extract and a step.
-- What a fused representation adds is a wiring decision — that the two
-- legs share one input wire and one tick.  'Cell' is the inventory as
-- data; 'Circuit.Body.Body' is the same machine with the wiring
-- soldered.
--
-- * __@t@ — tick tensor__: how the state is paired with the input on
--   'poke''s wire.  @(,)@ is simultaneous sharing; @Either@ and
--   @Data.These.These@ are schedules.  @t@ governs 'poke' only — 'peek'
--   has no input to be scheduled against.
-- * __@s@ — state__: the carrier.
-- * __@arr@ — base arrow__: usually @(->)@ or a Kleisli arrow @K m@.
--
-- Moore by construction: 'peek' never consults the input, so a 'Cell'
-- is a Moore machine by type, not by obligation.  Mealy behaviour — the
-- output consulting the current input — lives one floor down, in 'Body',
-- where the output and the input share an arrow.
--
-- At @t = (,)@, @arr = (->)@ a cell is a coalgebra for
-- @F X = b × X^a@: 'peek' and 'poke' curried together are
-- @s -> (b, a -> s)@, and the final coalgebra of that functor is the
-- causal stream functions.  The polynomial machine of
-- "Circuit.Machine" is this same record with the interface indexed by
-- @Poly@ — @(a, b)@ become @('Dir' p, 'Pos' p)@ — but nothing here
-- depends on that layer.
--
-- The moves between the two forms are asymmetric, and the asymmetry is
-- the Moore/Mealy distinction made visible in the API:
--
-- * 'fuse' is total but gated: the input wire must fork to feed both
--   legs, and forking is a capability the base arrow supplies, not an
--   ambient.
-- * 'unfuse' is total only by changing the carrier: the state grows a
--   slot for the most recent output, and the observation reads it one
--   tick late.
--
-- The pointed discharge of a cell — the seed as data — is
-- 'Circuit.Process.Process'; this module is where the two-leg shape
-- earns its place before the streaming layer is rebuilt on it.  It is
-- deliberately not re-exported by the umbrella "Circuit" module.
module Circuit.Cell
  ( -- * Two-leg cells
    Cell (..),

    -- * Wiring moves
    fuse,
    unfuse,
  )
where

import Circuit.Bimonoid (CopyT (..), Discard (..), DiscardT (..))
import Circuit.Body (Body (..))
import Circuit.Category (Category (..))
import Circuit.Tensor (Tensor (..), Unital (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Body (Body (..))

-- | A stateful cell: an observation and a step, unwired.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> peek c 3
-- 6
-- >>> poke c (3, 5)
-- 8
data Cell (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) a b = Cell
  { -- | The observation: read the output from the state alone.  Never
    -- consults the input — the Moore condition, here by construction.
    peek :: arr s b,
    -- | The step: the state paired with the input under the tick tensor
    -- @t@, consumed to write the next state.
    poke :: arr (t s a) s
  }

-- | Wire a cell into a 'Body': state and input in together under @t@,
-- state and output out together.
--
-- @
-- fuse (Cell peek poke) = Body (tensor poke (peek . project) . copyT)
--   where project = unitr . tensor id discardT
-- @
--
-- The input wire forks — one copy feeds 'poke', the other is projected
-- to the state and read by 'peek' — so fusion spends two capabilities
-- of the base arrow: 'Circuit.Bimonoid.CopyT' at the whole input, and
-- 'Circuit.Bimonoid.DiscardT' at the payload for the projection.  On a
-- cartesian base both are free; on a linear or relational one neither
-- is ambient, and neither is fusion.  At @t = Either@ the projection
-- has no arrow — a flowchart tick carries no fusible channel — and the
-- constraint correctly refuses.
--
-- The observation reads the /incoming/ state; a mutant that peeked the
-- stepped state would print @(8,16)@ below.
--
-- >>> let c = Cell (*2) (\(s, a) -> s + a) :: Cell (,) Int (->) Int Int
-- >>> morphism (fuse c) (3, 5)
-- (8,6)
fuse ::
  forall t s arr a b.
  (CopyT t arr (t s a), DiscardT t arr a) =>
  Cell t s arr a b ->
  Body t s arr a b
fuse (Cell peek poke) =
  Body (tensor poke (peek . unitr . tensor id (discardT @t)) . copyT)

-- | Unfuse a 'Body' into a cell, at the price of the carrier.
--
-- A fused body may consult the input when choosing its output — Mealy
-- behaviour — so no cell over the same state can present it.  The
-- carrier grows a slot for the most recent output: 'poke' stores the
-- body's whole result, 'peek' reads the slot back.  Both new wires
-- discard, and the constraint says so.  This is the state-enlargement
-- 'Circuit.Process.bodyToMoore' and 'Circuit.Process.mealy' already
-- use.
--
-- >>> let adder = Body (\(s, a) -> (s + a, s)) :: Body (,) Int (->) Int Int
-- >>> peek (unfuse adder) (8, 3)
-- 3
-- >>> poke (unfuse adder) ((8, 3), 5)
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
unfuse ::
  (Tensor (,) arr, Discard arr s, Discard arr b) =>
  Body (,) s arr a b ->
  Cell (,) (s, b) arr a b
unfuse (Body f) =
  Cell
    (unitl . tensor discard id)
    (f . tensor (unitr . tensor id discard) id)

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- == Tutorial
--
-- This module re-exports the whole public API, grouped into four sections.
-- One counter runs through all of them — @n + i@ accumulating, observed at
-- @n@ — built up from a bare function to a closed feedback loop.
--
-- === Arrows: what circuits are made of
--
-- "Circuit.Category" is the local category hierarchy: composition, poles
-- for products and coproducts, no object constraints. "Circuit.Tensor" is
-- the tensor action and braiding. "Circuit.Traced" chooses the feedback
-- discipline: lazy knots over @(,)@, terminating iteration over `Either`,
-- scheduling over `Data.These.These`. "Circuit.Bimonoid" is the bimonoid
-- layer of circuit wiring, copy and discard. "Circuit.Rel" is finite
-- relations, the reference semantics in two grades.
--
-- The counter at this level is a bare function, an update paired with an
-- observation:
--
-- >>> let counter (n, i) = (n + i, n)
-- >>> counter (0, 1)
-- (1,0)
--
-- Over the @(,)@ tensor the feedback value and the output are produced
-- simultaneously, which ties a lazy knot:
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> yank powers () :: [Integer]
-- [1,2,4,8,16]
--
-- Over `Either` the loop ends when the body answers `Right`:
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> yank (either step step) (0 :: Int)
-- 5
--
-- === Syntax: free constructions
--
-- "Circuit.Syntax" is the generic substrate: signatures, free layers,
-- folds (@run@, @eval@, @bind@) and injections (@unit@, @Lift@).
-- "Circuit.Trace" adds feedback to the free syntax, making it traced.
-- "Circuit.Net" packages the free symmetric monoidal category with a
-- bimonoid over a primitive set. "Circuit.Body" is the knot-body
-- category @arr (t ch a) (t ch b)@ — the stateful substrate that tracing
-- hides. "Circuit.Hyper" is the final, coinductive encoding.
-- "Circuit.Span" is finite spans, the residual-remembering rung of the
-- equipment ladder.
--
-- As a body, the counter is one morphism @arr (Int, Int) (Int, Int)@:
--
-- >>> let counterBody = Body (\(n, i) -> (n + i, n)) :: Body (,) Int (->) Int Int
-- >>> scan (bodyToMoore counterBody 0) [1,1,1]
-- [0,1,2]
--
-- Note the body runner observes before the state updates; the machine
-- runners below observe after.
--
-- The same wiring can be written in free syntax and run. `widen` embeds
-- the primitive layer into the net; `run` folds the net back down:
--
-- >>> let m = Lift (*2) .> Lift (+1) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- @Trace@ is the inspectable free-syntax form; @Hyper@ is the final
-- encoding. Convert with `encode`, observe with `observe`:
--
-- >>> observe (encode (Lift (+1) :: Trace (,) (->) Int Int)) 41
-- 42
--
-- === Machines: stateful observations
--
-- "Circuit.Machine" views a stateful device as a machine fibered over a
-- polynomial interface @p@. "Circuit.Process" supplies the runners: the
-- unpointed `Moore` carrier, the pointed `Process` carrier, and scans.
-- "Circuit.Stream" is the neutral stream interface, `Uncons` against
-- `Cons` and `Snoc`.
--
-- As a machine, the counter exposes its observation as a polynomial
-- position, so the observation is read without stepping:
--
-- >>> let counter = moore (\n -> (n, ())) (\n d -> n + monoDir d) :: MachineObs Int (Mono Int Int)
-- >>> scan (machineAsMoore counter 0) [1,1,1]
-- [1,2,3]
--
-- A machine converts to a process, the pointed stream carrier:
--
-- >>> scanProcess (asProcess counter 0) [1,1,1]
-- [1,2,3]
--
-- Or the seed is handed in as data, a `UnitCell`, instead of an argument:
--
-- >>> scanProcess (asProcessCell counter (UnitCell (const 0))) [1,1,1]
-- [1,2,3]
--
-- Two machines run side by side over the tensor of their interfaces,
-- state tensored:
--
-- >>> let both = parWiringMachine counter counter :: MachineObs (Int, Int) (PTensor (Mono Int Int) (Mono Int Int))
-- >>> moStep both (0, 10) (monoIn 1, monoIn 1)
-- (1,11)
-- >>> moObserve both (0, 10)
-- ((0,()),(10,()))
--
-- Finally the machine closes into a feedback loop: `machineToClosed`
-- folds the carrier into the feedback wire of a `Trace`, and the seed is
-- gone from the type. The leaky counter — state replaced by the input
-- each tick — has a knot solution:
--
-- >>> let leaky = machineObs (\s -> EP (EK (s + 1), EE (\i -> i))) :: MachineObs Int (Mono Int Int)
-- >>> eval (machineToClosed (moMachine leaky)) (Right 5 :: Dir (Mono Int Int))
-- (6,())
--
-- The true accumulator has none: its next state depends on the current
-- one, and the lazy knot over @(,)@ diverges. The Axioma suite pins that
-- with its divergence oracle.
--
-- === Helpers: equipment
--
-- "Circuit.Equip" is the arrow-equipment surface: channel poles, squares,
-- boundary tokens, and the `UnitCell` pointing taxonomy. "Circuit.Poly"
-- is the category @Poly@ of polynomials. "Circuit.Optic" is mixed optics
-- as residual maps. "Circuit.Container" is the container view —
-- @Eval p x@ as a position with the pins of that position assigned.
-- "Circuit.Linear" is linear-logic connectives over a base category.
-- "Circuit.Shared" fuses two bodies on one shared channel.
-- "Circuit.Pullback" is linear cotangent maps, the base arrow for
-- reverse-mode gradients.
--
-- A 'Poles' pair over the unit carrier closes with 'box' to a plain
-- morphism, and a closed morphism lifts straight into a body:
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () (->) () Int
-- >>> box p ()
-- 42
-- >>> let b = Body (\((), ()) -> ((), box p ())) :: Body (,) () (->) () Int
-- >>> morphism b ((), ())
-- ((),42)
--
-- Processes and lenses interconvert; the round trip is the identity on
-- runs:
--
-- >>> let acc = Process 0 (\s i -> s + i) (\s -> s * 2) :: Process Int Int Int
-- >>> scanProcess (lensAsProcess (processAsLens acc) 0) [1,2,3]
-- [2,6,12]
--
-- Pullback nets compose as cotangent chains — the circuits-diff name for
-- this is reverse mode:
--
-- >>> evalPullback (Lift (Pullback (* 2)) .> Lift (Pullback (* 3)) :: Net (,) Pullback Int Int) 1
-- 6
--
-- At the container grade the monomial's fibre is flat: the direction at a
-- boundary branch equals the direction itself, witnessed on the nose:
--
-- >>> case monoFibreFlat of Refl -> "fibre is flat"
-- "fibre is flat"
--
-- == Usage
--
-- The library brings its own 'id' and '(.)'. Importing it unqualified
-- alongside 'Prelude' requires hiding the duplicates:
--
-- @
-- import Prelude hiding (id, (.))
-- import Circuit
-- @
--
-- == What is not covered
--
-- This tutorial stops at the API surface. It does not argue the gap
-- between the free syntax and its reference semantics — that check lives
-- in the circuits-axioma suite — and it does not render anything: no
-- string diagrams, no pictures.
module Circuit
  ( -- * Arrows
    module Circuit.Category,
    module Circuit.Traced,
    module Circuit.Tensor,
    module Circuit.Bimonoid,
    module Circuit.Rel,

    -- * Syntax
    module Circuit.Syntax,
    module Circuit.Trace,
    module Circuit.Net,
    module Circuit.Body,
    module Circuit.Hyper,
    module Circuit.Span,

    -- * Machines
    module Circuit.Machine,
    module Circuit.Process,
    module Circuit.Stream,

    -- * Helpers
    module Circuit.Equip,
    module Circuit.Poly,
    module Circuit.Optic,
    module Circuit.Container,
    module Circuit.Linear,
    module Circuit.Shared,
    module Circuit.Pullback,
  )
where

import Circuit.Bimonoid
import Circuit.Body
import Circuit.Category
import Circuit.Container
import Circuit.Equip
import Circuit.Hyper
import Circuit.Linear
import Circuit.Machine
import Circuit.Net
import Circuit.Optic
import Circuit.Poly
import Circuit.Process
import Circuit.Pullback
import Circuit.Rel
import Circuit.Shared
import Circuit.Span
import Circuit.Stream
import Circuit.Syntax
import Circuit.Tensor
import Circuit.Trace
import Circuit.Traced
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XDataKinds -XLambdaCase
-- >>> import Prelude hiding (id, (.))
-- >>> import Circuit
-- >>> import Data.Type.Equality ((:~:) (Refl))

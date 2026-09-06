{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The arrow-equipment surface: channel poles, squares, and boundary tokens.
--
-- In the proarrow-equipment reading of the library the tight arrows are the
-- base @arr@ morphisms and the loose arrows are 'Circuit.Body.Body' values
-- (a body @arr (t ch a) (t ch b)@ with its carrier @ch@ exposed).  This
-- module holds the equipment furniture:
--
-- * channel poles: 'Poles', the companion/conjoint pair of an identity
--   with an explicit carrier @ch@, and its fully general form 'SplitPoles'
--   when the write and read legs sit at different carriers or in different
--   base categories;
-- * polar ends: 'In' and 'Out', the conjoint and companion of the
--   identity functor as rank-2 poles, paired by 'PolesIO';
-- * squares: the indexed 2-cell 'Sq' and its existential closure 'TwoCell';
-- * boundary tokens: 'Boundary' (mark or payload) and 'Stamped'
--   (occurrence-stamped values).
--
-- The loose side composes by 'Circuit.Body.seqCompose' over the tensor,
-- and the would-be monoidal laws hold only after transporting carriers by
-- the tensor's structural maps: carriers @ch ⊗ (ch' ⊗ ch'')@ and
-- @(ch ⊗ ch') ⊗ ch''@ are different Haskell types, so on-the-nose
-- associativity is impossible.  A 'Sq' record bundles such a transport
-- with two bodies; the commuting of the square is a caller side condition,
-- checked for the named witnesses by sampled oracles in @Axioma.Equip@.
-- What is not claimed: no globular 2-cells between bodies, no inverse
-- witnesses, no triangle or pentagon — the loose side is not packaged as a
-- pseudo-bicategory, only as a composition operator with named transports
-- and per-instance checked equations.
module Circuit.Equip
  ( -- * Channel poles
    Poles (..),
    close,
    plug,

    -- * Split poles (different carriers or bases per leg)
    SplitPoles (..),
    plugBridge,
    closeBridge,

    -- * Unit-pole convenience
    poles0,
    polesK,
    splay0,

    -- * Sequential composition
    compose,
    compose0,

    -- * Parallel composition
    polesTensor,

    -- * Morphism-level mapping
    iomap,
    imap,
    omap,

    -- * Polar ends (companion / conjoint of the identity)
    Out (..),
    In (..),
    PolesIO (..),
    prefixIn,
    suffixOut,

    -- * Unit poles and copycat
    open,
    copycat,

    -- * Unit cells
    UnitCell (..),
    pointedCell,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Additive connectives
    pair,
    race,

    -- * Companion / conjoint of a tight arrow
    companionTight,
    conjointTight,

    -- * Indexed 2-cell (carrier map + commuting square)
    Sq (..),
    idSq,
    vcomp,

    -- * Existential closure of Sq
    TwoCell (..),
    withTwoCell,

    -- * The two paths whose equality is the square
    downThenAcross,
    acrossThenDown,
    checkSq,

    -- * Structural proof witnesses (unitors and associator)
    unitorLeft,
    unitorRight,
    unitorLeftSq,
    unitorRightSq,
    associator,
    associatorSq,

    -- * Horizontal 2-cell algebra
    rightWhisker,
    leftWhisker,
    hcompose,
    whiskerSq,

    -- * Boundary tokens
    Boundary (..),
    isMark,
    isPayload,
    Stamped (..),
  )
where

import Circuit.Bimonoid (Copy (copy))
import Circuit.Body (Body (..), seqCompose)
import Circuit.Category (Category (..), CoK (..), FunctionLike (..), K (..), Pointed (..), (.>))
import Circuit.Tensor (Bias (..), Tensor (..), Unit, Unital (..))
import Circuit.Tensor qualified as Tensor
import Circuit.Traced (Assoc (..), Strength (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Body (Body (..))
-- >>> import Circuit.Category (CoK (..), K (..), runK, (.>))
-- >>> import Circuit.Equip
-- >>> import Circuit.Tensor (Bias (..))
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Maybe (isNothing)
-- >>> :{
-- let copycatIO :: PolesIO (->) () ()
--     copycatIO = PolesIO { conjointIO = In (\o a -> emit o (conjointIO copycatIO) a)
--                         , companionIO = Out (\_ _ -> ()) }
-- :}

-- * Channel poles — the companion and conjoint of the identity functor.

-- | A matched pair of channel poles with a shared carrier and base.
--
-- @conjoint@ is the write leg: it consumes the input payload and produces
-- the channel, in the base @arr@.  @companion@ is the read leg: it consumes
-- the channel and produces the output payload, in the same base.  This is
-- the default spelling; when the two legs must sit at different carriers
-- or in different base categories, use 'SplitPoles'.
--
-- When the pole is self-channelled, 'close' plugs the two legs.  Note
-- 'plug' takes a 'SplitPoles': translating between two carriers of one
-- pole is a split-carrier situation by definition.
data Poles ch arr a b = Poles
  { -- | Write leg (conjoint), producing the channel @ch@.
    conjoint :: arr a ch,
    -- | Read leg (companion), consuming the channel @ch@.
    companion :: arr ch b
  }

-- | The fully general pole: split carrier, split base.
--
-- The write leg produces the write channel @ch@ in base @arrW@; the read leg
-- consumes the read channel @ch'@ in base @arrR@.  The split is needed when
-- the two legs live in different categories — a Kleisli write against a
-- co-Kleisli read, as in 'plugBridge' — or at different carriers ('plug'
-- inserts a translation; 'boxAsymmetric' exposes the two carriers on
-- opposite sides of the box).  'Poles' is the diagonal specialisation
-- @ch ~ ch', arrW ~ arrR@ and the default spelling.
data SplitPoles ch ch' arrW arrR a b = SplitPoles
  { -- | Write leg (conjoint), producing the write channel @ch@.
    splitConjoint :: arrW a ch,
    -- | Read leg (companion), consuming the read channel @ch'@.
    splitCompanion :: arrR ch' b
  }

-- | Generalised polar plug.
--
-- 'plug' inserts a translation @m :: arr ch ch'@ between the write leg and
-- the read leg of a single-base 'SplitPoles', producing a morphism
-- @arr a b@.
--
-- >>> let p = SplitPoles (const ()) (const 42) :: SplitPoles () () (->) (->) () Int
-- >>> plug id p ()
-- 42
plug :: (Category arr) => arr ch ch' -> SplitPoles ch ch' arr arr a b -> arr a b
plug m p = splitConjoint p .> m .> splitCompanion p

-- | Close a same-carrier 'Poles' by composing its two legs.
--
-- With a single carrier there is no gap to translate, so the payload types
-- are free; @close (copycat \@ch)@ is the identity at any carrier.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () (->) () Int
-- >>> close p ()
-- 42
close :: (Category arr) => Poles ch arr a b -> arr a b
close p = conjoint p .> companion p

-- | Close a split-base pole through a bridge.
--
-- The write leg is Kleisli (@a -> m ch@), the read leg is co-Kleisli
-- (@c ch' -> b@), and closing demands a bridge @m ch -> c ch'@ between the
-- monad and the comonad.  The bridge is where any seed or choice the
-- carrier needs must be supplied.
--
-- >>> let p = SplitPoles (K (Identity . (+1))) (CoK runIdentity) :: SplitPoles Int Int (K Identity) (CoK Identity) Int Int
-- >>> plugBridge id p 5
-- 6
plugBridge :: (m ch -> c ch') -> SplitPoles ch ch' (K m) (CoK c) a b -> a -> b
plugBridge bridge p a = runCoK (splitCompanion p) (bridge (runK (splitConjoint p) a))

-- | 'plugBridge' at a self-channelled carrier.
closeBridge :: (m ch -> c ch) -> SplitPoles ch ch (K m) (CoK c) a b -> a -> b
closeBridge bridge = plugBridge bridge

-- * Unit-pole convenience

-- | Build a unit-channel pole from a write morphism and a read morphism.
--
-- @poles0 write receive = Poles write receive :: Poles () () arr arr a b@.
poles0 ::
  forall arr a b.
  arr a () ->
  arr () b ->
  Poles () arr a b
poles0 = Poles
{-# INLINE poles0 #-}

-- | Specialization of 'poles0' for @K@ actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@ produces
-- the output payload.
polesK ::
  forall m a b.
  (a -> m ()) ->
  m b ->
  Poles () (K m) a b
polesK write receive = Poles (K write) (K $ const receive)

-- | Extract the primitive write and read actions from a unit-channel pole.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () (->) () Int
-- >>> let (w, r) = splay0 p
-- >>> (w (), r ())
-- ((),42)
splay0 ::
  forall arr a b.
  Poles () arr a b ->
  (arr a (), arr () b)
splay0 p = (conjoint p, companion p)

-- * Sequential composition

-- | Sequential composition of 'Poles'.
--
-- The read leg of the first pole is chained through the payload to the write
-- leg of the second pole.  No channel alignment is required: each pole keeps
-- its own carrier, and all legs share one base.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () (->) Int Int
-- >>> close (compose p1 p2) ()
-- 2
compose ::
  (Category arr) =>
  Poles ch1 arr a b ->
  Poles ch2 arr b c ->
  Poles ch1 arr a c
compose p1 p2 =
  Poles
    (conjoint p1)
    (companion p1 .> conjoint p2 .> companion p2)

-- | Convenience synonym for 'compose' on unit-channel poles.
compose0 ::
  (Category arr) =>
  Poles () arr a b ->
  Poles () arr b c ->
  Poles () arr a c
compose0 = compose
{-# INLINE compose0 #-}

-- * Parallel composition

-- | Parallel composition of 'Poles' over a tensor @t@.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () (->) () Int
-- >>> close (polesTensor p1 p2) ((),())
-- (1,2)
polesTensor ::
  forall t arr ch1 ch2 a b c d.
  (Tensor t arr) =>
  Poles ch1 arr a b ->
  Poles ch2 arr c d ->
  Poles (t ch1 ch2) arr (t a c) (t b d)
polesTensor p1 p2 =
  Poles
    (Tensor.tensor (conjoint p1) (conjoint p2))
    (Tensor.tensor (companion p1) (companion p2))

-- * Morphism-level mapping

-- | Precompose the input and postcompose the output.
iomap ::
  forall arr a a' b b' ch.
  (Category arr) =>
  arr a' a ->
  arr b b' ->
  Poles ch arr a b ->
  Poles ch arr a' b'
iomap f g (Poles i o) = Poles (f .> i) (o .> g)

-- | Precompose the input.
imap ::
  forall arr a a' b ch.
  (Category arr) =>
  arr a' a ->
  Poles ch arr a b ->
  Poles ch arr a' b
imap f (Poles i o) = Poles (f .> i) o

-- | Postcompose the output.
omap ::
  forall arr a b b' ch.
  (Category arr) =>
  arr b b' ->
  Poles ch arr a b ->
  Poles ch arr a b'
omap g (Poles i o) = Poles i (o .> g)

-- * Polar ends — the companion and conjoint of the identity functor.

-- | @Out@ is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
--
-- The rank-2 field quantifies over the opposing pole's payload: an
-- @Out arr a@ produces an @a@ once supplied with any 'In' pole.
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other pole.
    emit :: forall x. In arr x -> arr x a
  }

-- | @In@ is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
--
-- Dually, an @In arr a@ consumes an @a@ once supplied with any 'Out'
-- pole.
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other pole.
    --
    -- Every 'In' pole is already a polymorphic consumer of 'Out' poles, so
    -- commit is the counit of the polar pairing, without any same-type
    -- restriction:
    --
    -- >>> let out42 = suffixOut (companionIO copycatIO) (const 42) :: Out (->) Int
    -- >>> let inS = prefixIn (const ()) (conjointIO copycatIO) :: In (->) String
    -- >>> commit inS out42 "hello"
    -- 42
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel poles: one 'In' and one 'Out'.
--
-- The conjoint ('conjointIO') consumes payloads of type @a@; the
-- companion ('companionIO') produces payloads of type @b@.  For
-- symmetric channels such as queues @a = b@.
--
-- Together with 'prefixIn' and 'suffixOut', @PolesIO@ carries an
-- /enriched/ profunctor structure over the base category @arr@:
-- 'prefixIn' is the left action of @arr@ on 'In' poles, and 'suffixOut'
-- is the right action of @arr@ on 'Out' poles.
data PolesIO arr a b = PolesIO
  { -- | Write pole (producer), the conjoint.
    conjointIO :: In arr a,
    -- | Read pole (consumer), the companion.
    companionIO :: Out arr b
  }

-- | Precompose an @arr@-morphism with an 'In' pole.
--
-- Given @f :: arr a b@ and an 'In' pole at type @b@, produce an 'In'
-- pole at type @a@.  Running the resulting pole first executes @f@ and
-- then commits through the original pole.
--
-- This is the left (contravariant) action of the base category on 'In'
-- poles.  Specialised to unit poles it is the canonical way to build
-- effectful write poles.
prefixIn :: forall arr a b. (Category arr) => arr a b -> In arr b -> In arr a
prefixIn f i = In $ \(o :: Out arr x) -> f .> commit i o

-- | Postcompose an @arr@-morphism with an 'Out' pole.
--
-- Given an 'Out' pole at type @a@ and @g :: arr a b@, produce an 'Out'
-- pole at type @b@.  Running the resulting pole first emits through the
-- original pole and then executes @g@ on the emitted value.
--
-- This is the right (covariant) action of the base category on 'Out'
-- poles.  Specialised to unit poles it is the canonical way to build
-- effectful read poles.
suffixOut :: forall arr a b. (Category arr) => Out arr a -> arr a b -> Out arr b
suffixOut o g = Out $ \(i :: In arr x) -> emit o i .> g

-- * Unit poles and copycat

-- | Unit poles at the monoidal unit @()@.
--
-- The write leg discards its input; the read leg discards its channel.
-- Yanking recovers the identity on @()@.
--
-- >>> let p = open :: Poles () (->) () ()
-- >>> close p ()
-- ()
open :: (Category arr) => Poles () arr () ()
open = Poles id id

-- | The copycat strategy at any carrier.
--
-- With identity legs, closing is the identity on the carrier.
--
-- >>> close (copycat :: Poles Bool (->) Bool Bool) True
-- True
copycat :: (Category arr) => Poles ch arr ch ch
copycat = Poles id id

-- * Unit cells

-- | A unit cell: an arrow out of the monoidal unit, @arr (Unit t) ch@.
--
-- Pointing is forced exactly where a carrier must be instantiated and no
-- input supplies it. There are three discharges, and this type is the
-- explicit one:
--
-- * input: the first payload seeds the carrier — 'Circuit.Process.asMoore'
--   removes the seed of a 'Circuit.Process.Process';
-- * closure: the loop seeds itself — 'Circuit.Machine.machineToClosed'
--   removes the carrier of a 'Circuit.Machine.Machine' via
--   'Circuit.Trace.yank', and the seed is gone from the type;
-- * explicit: the seed is data, handed to runners such as
--   'Circuit.Process.asProcessCell' or @'Circuit.Process.scan' composed
--   with 'Circuit.Process.bodyToMoore'.
--
-- The same pointing is independently present at each open post: the seed
-- argument of a 'Circuit.Process.bodyToMoore' run, the initial state of a
-- 'Circuit.Machine.Machine' run, the seed field of 'Circuit.Process.Process',
-- the 'Circuit.Category.Pointed' class, the unit pole 'open'. 'Pointed' is
-- the EM side (an algebra of the @Maybe@ monad, structure on the object);
-- 'UnitCell' is the same pointing as a value.
--
-- Constraint map: a cell is required exactly where a carrier must be
-- instantiated and no input supplies it (Loregian: every missing colimit
-- in the process equipment is a carrier that would have to be pointed or
-- singleton). Open layers need one: body runners, machine runs,
-- 'Process', 'Either'-carried unit loops. Closed layers need none, by
-- type: 'yank' folds (self-seeding at @(,)@, starting from the input at
-- 'Either'), flowchart runners, 'machineToClosed'.
newtype UnitCell (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) ch = UnitCell
  { runUnitCell :: arr (Unit t) ch
  }

-- | A 'Circuit.Category.Pointed' carrier has the canonical cell.
--
-- >>> runUnitCell (pointedCell :: UnitCell (,) (->) ()) ()
-- ()
pointedCell :: (Pointed ch) => UnitCell (,) (->) ch
pointedCell = UnitCell (\() -> point)

-- * Boxes

-- | Close a unit-channel 'Poles' to a plain morphism.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () (->) () Int
-- >>> box p ()
-- 42
box :: (Category arr) => Poles () arr a b -> arr a b
box p = conjoint p .> companion p

-- | Asymmetric box with the channel exposed on opposite sides.
--
-- The write carrier appears on the output side and the read carrier on the
-- input side, so this is a 'SplitPoles' operation.
--
-- >>> let p = SplitPoles (const ()) (const 42) :: SplitPoles () () (->) (->) () Int
-- >>> boxAsymmetric p ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr ch ch' a b.
  (Tensor t arr) =>
  SplitPoles ch ch' arr arr a b ->
  arr (t a ch') (t ch b)
boxAsymmetric p = Tensor.tensor (splitConjoint p) (splitCompanion p)

-- * Additive connectives

-- | Additive conjunction: both sub-poles receive the same input and their
-- outputs are paired.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () (->) () Int
-- >>> close (pair p1 p2) ()
-- (1,2)
pair ::
  forall arr ch1 ch2 a b c.
  (Tensor (,) arr, Copy arr a) =>
  Poles ch1 arr a b ->
  Poles ch2 arr a c ->
  Poles (ch1, ch2) arr a (b, c)
pair p1 p2 =
  Poles
    (copy .> Tensor.tensor (conjoint p1) (conjoint p2))
    (Tensor.tensor (companion p1) (companion p2))

-- | Additive disjunction / race: both sub-poles receive the same input, but
-- only the first output satisfying the predicate is emitted.
--
-- The predicate selects "silent" values that should be skipped. The bias
-- chooses which side to prefer when both are non-silent. The picking logic is
-- lifted into the base arrow via 'FunctionLike'.
--
-- >>> let eL = Poles (const ()) (const (Just 1)) :: Poles () (->) () (Maybe Int)
-- >>> let eR = Poles (const ()) (const (Just 2)) :: Poles () (->) () (Maybe Int)
-- >>> close (race isNothing LeftFirst eL eR) ()
-- Just 1
-- >>> close (race isNothing RightFirst eL eR) ()
-- Just 2
race ::
  forall arr ch1 ch2 a b.
  (Tensor (,) arr, Copy arr a, FunctionLike arr) =>
  (b -> Bool) ->
  Bias ->
  Poles ch1 arr a b ->
  Poles ch2 arr a b ->
  Poles (ch1, ch2) arr a b
race isSilent bias p1 p2 = omap (function (pick bias)) (pair p1 p2)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- * Companion / conjoint of a tight arrow

-- | The companion of a tight arrow.
--
-- The companion of @f :: arr a b@ is the pole with identity write leg and
-- read leg @f@.
--
-- >>> box (companionTight (const 42 :: () -> Int)) ()
-- 42
companionTight :: (Category arr) => arr a b -> Poles a arr a b
companionTight f = Poles id f

-- | The conjoint of a tight arrow.
--
-- The conjoint of @f :: arr a b@ is the pole with write leg @f@ and identity
-- read leg.
--
-- >>> box (conjointTight (const () :: Int -> ())) 7
-- ()
conjointTight :: (Category arr) => arr a b -> Poles b arr a b
conjointTight f = Poles f id

-- * Squares

-- | Square (indexed 2-cell).  The carrier maps compose; the middle body must
-- match (a caller side condition, decidable on samples via 'checkSq').
data Sq t arr ch ch' a b = Sq
  { -- | Map between carriers.
    carrierMap :: arr ch ch',
    -- | Source body, over the source carrier.
    sqSrc :: Body t ch arr a b,
    -- | Target body, over the target carrier.
    sqTgt :: Body t ch' arr a b
  }

-- | Identity square on a body.
idSq :: (Category arr) => Body t ch arr a b -> Sq t arr ch ch a b
idSq b = Sq id b b

-- | Vertical composition of squares.
--
-- The dropped middle bodies (@sqTgt f@ and @sqSrc g@, on the shared middle
-- carrier) must agree — a caller side condition, since the operator is
-- generic in the arrow.  'checkSq' decides agreement on samples for @(->)@
-- bodies.  Note the composite's own legs are @sqSrc f@ and @sqTgt g@: when
-- the middle carrier differs from both outer carriers, the composite's
-- paths never force the middle bodies to agree, so check the factors there
-- rather than the composite.
vcomp ::
  (Category arr) =>
  Sq t arr ch' ch'' a b ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch'' a b
vcomp g f = Sq (carrierMap f .> carrierMap g) (sqSrc f) (sqTgt g)

-- | Existential closure of 'Sq', for stating "there exists a 2-cell".
data TwoCell t arr a b where
  TwoCell :: Sq t arr ch ch' a b -> TwoCell t arr a b

-- | Eliminator for the existential carrier types of a 'TwoCell'.
withTwoCell ::
  TwoCell t arr a b ->
  (forall ch ch'. Sq t arr ch ch' a b -> r) ->
  r
withTwoCell (TwoCell sq) k = k sq

-- | Go down (carrier map) then across (target body).
--
-- A nondegenerate two-cell witness: counter state quotiented by parity.
-- The payload is 'Char' so the carrier slot and payload slot are type-distinct;
-- slot confusion is a type error.  These examples exercise both parities and
-- both reset branches.  A paired perturbation doctest on 'acrossThenDown'
-- shows the equality can fail, so these agreement cases are not vacuous.
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross sq (4, False)
-- (True,'x')
-- >>> downThenAcross sq (4, True)
-- (False,'y')
-- >>> downThenAcross sq (5, False)
-- (False,'y')
downThenAcross ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
downThenAcross sq = tensor (carrierMap sq) id .> morphism (sqTgt sq)

-- | Go across (source body) then down (carrier map).
--
-- Agreement cases for the same witness:
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> acrossThenDown sq (4, False)
-- (True,'x')
-- >>> acrossThenDown sq (4, True)
-- (False,'y')
-- >>> acrossThenDown sq (5, False)
-- (False,'y')
--
-- Perturbation: observe even-ness instead of odd-ness.  The two paths now
-- disagree, which proves the agreement cases above are not vacuous.
--
-- >>> let badCounter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let bad = Sq odd badCounter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross bad (4, False)
-- (True,'x')
-- >>> acrossThenDown bad (4, False)
-- (True,'y')
acrossThenDown ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
acrossThenDown sq = morphism (sqSrc sq) .> tensor (carrierMap sq) id

-- | Sampled agreement check for a square: run both paths ('acrossThenDown'
-- and 'downThenAcross') across the samples and compare.  This is the
-- decidable fragment of the "middle body must match" side condition on
-- 'Sq' and 'vcomp', for @(->)@ bodies with equality-comparable outputs.
--
-- The nondegenerate witness passes:
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> checkSq [(4, False), (4, True), (5, False)] sq
-- True
--
-- The perturbed witness fails on the same samples:
--
-- >>> let badCounter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let bad = Sq odd badCounter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> checkSq [(4, False)] bad
-- False
checkSq ::
  (Tensor t (->), Eq (t ch' b)) =>
  [t ch a] ->
  Sq t (->) ch ch' a b ->
  Bool
checkSq samples sq = all (\x -> acrossThenDown sq x == downThenAcross sq x) samples

-- | Indexed left unitor square.
unitorLeftSq ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t (Unit t) ch) ch a b
unitorLeftSq b = Sq unitl (seqCompose b (Body id)) b

-- | Left unitor witness: composing a body with the identity at the unit carrier
-- is isomorphic to the original body.
unitorLeft ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  TwoCell t arr a b
unitorLeft b = TwoCell (unitorLeftSq b)

-- | Indexed right unitor square.
unitorRightSq ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t ch (Unit t)) ch a b
unitorRightSq b = Sq unitr (seqCompose (Body id) b) b

-- | Right unitor witness.
unitorRight ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  TwoCell t arr a b
unitorRight b = TwoCell (unitorRightSq b)

-- | Indexed associator square.
associatorSq ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  Sq t arr (t (t ch1 ch2) ch3) (t ch1 (t ch2 ch3)) a d
associatorSq h g f =
  Sq
    assoc
    (seqCompose h (seqCompose g f))
    (seqCompose (seqCompose h g) f)

-- | Associator witness: carrier bracketing of three composed bodies is
-- isomorphic up to the associator of the tensor.
associator ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  TwoCell t arr a d
associator h g f = TwoCell (associatorSq h g f)

-- | Right whisker: tensor a square with an identity-on-boundaries 1-cell on
-- the right.
rightWhisker ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch ch' a b ->
  Body t d arr b c ->
  Sq t arr (t ch d) (t ch' d) a c
rightWhisker sq r =
  Sq
    (tensor (carrierMap sq) id)
    (seqCompose r (sqSrc sq))
    (seqCompose r (sqTgt sq))

-- | Left whisker: tensor an identity-on-boundaries 1-cell on the left of a
-- square.
leftWhisker ::
  (Tensor t arr, Strength t arr) =>
  Body t d arr a' a ->
  Sq t arr ch ch' a b ->
  Sq t arr (t d ch) (t d ch') a' b
leftWhisker l sq =
  Sq
    (tensor id (carrierMap sq))
    (seqCompose (sqSrc sq) l)
    (seqCompose (sqTgt sq) l)

-- | Horizontal composition of two squares.
hcompose ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch2 ch2' b c ->
  Sq t arr ch1 ch1' a b ->
  Sq t arr (t ch1 ch2) (t ch1' ch2') a c
hcompose sq2 sq1 =
  Sq
    (tensor (carrierMap sq1) (carrierMap sq2))
    (seqCompose (sqSrc sq2) (sqSrc sq1))
    (seqCompose (sqTgt sq2) (sqTgt sq1))

-- | Boundary whisker: apply tight maps to the input and output boundaries of a
-- square.  This is the 'Sq' side of the interchange law; the 'Poles' side is
-- 'iomap' on the explicit-carrier representation.
whiskerSq ::
  (Tensor t arr) =>
  arr a' a ->
  arr b b' ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch' a' b'
whiskerSq f g sq =
  Sq
    (carrierMap sq)
    (Body $ tensor id f .> morphism (sqSrc sq) .> tensor id g)
    (Body $ tensor id f .> morphism (sqTgt sq) .> tensor id g)

-- * Boundary tokens

-- | The free boundary @K + payload@.
--
-- A token on the boundary is either a mark from a finite alphabet @k@ or a
-- payload value @a@.  This is the level-0 grammar of process boundaries:
-- marks are the control tokens, payloads are the data.
--
-- 'fmap' acts only on the payload side; marks are carried through unchanged.
--
-- >>> fmap length (Payload "hi")
-- Payload 2
-- >>> fmap length (Mark "halt")
-- Mark "halt"
data Boundary k a
  = -- | Control token from the finite mark alphabet.
    Mark k
  | -- | Data-carrying payload.
    Payload a
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Boundary where
  bimap f _ (Mark k) = Mark (f k)
  bimap _ g (Payload a) = Payload (g a)

-- | True iff the token is a 'Mark'.
isMark :: Boundary k a -> Bool
isMark (Mark _) = True
isMark (Payload _) = False

-- | True iff the token is a 'Payload'.
isPayload :: Boundary k a -> Bool
isPayload (Mark _) = False
isPayload (Payload _) = True

-- | Occurrence-tokens for values.
--
-- A 'Stamped' value pairs an occurrence token (a /stamp/) with a payload.
-- The stamp is an observation receipt: an id, a timestamp, a line number,
-- or any other token that names the occurrence without changing the
-- payload's meaning.
--
-- === Free theorem
--
-- The stamp is untouched by payload mapping:
--
-- @
-- stamp (fmap f s) = stamp s
-- stamped (fmap f s) = f (stamped s)
-- @
--
-- >>> let s = Stamped 42 "hello"
-- >>> stamp (fmap reverse s)
-- 42
-- >>> stamped (fmap reverse s)
-- "olleh"
data Stamped r a = Stamped
  { -- | Occurrence token / receipt.  Not touched by 'fmap'.
    stamp :: r,
    -- | The labelled payload.
    stamped :: a
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Stamped where
  bimap f g (Stamped r a) = Stamped (f r) (g a)

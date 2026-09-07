{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The bimonoid layer of circuit wiring.
--
-- This module collects the algebraic structure that every wire may carry in a
-- circuit category:
--
-- * 'Copy' / 'Discard' — the comonoid on channel objects (fan-out / weakening).
-- * 'Merge' / 'Zero' — the monoid on channel objects (fan-in / introduction).
-- * 'Bimonoid' — all four together, the precondition for 'Circuit.Net.mirrorNet'
--   to be total on a cartesian base arrow.
--
-- For a generic wiring tensor @t@ the tensor-generic classes 'CopyT',
-- 'DiscardT', 'MergeT' and 'ZeroT' play the same role.  The cartesian classes
-- are the special case @t = (,)@, recovered via the @OVERLAPPABLE@ default
-- instances at the bottom of this module.
--
-- The module also hosts the free dagger category ('Dagger', 'transpose'):
-- a value pairs a forward arrow with a backward arrow, composition runs
-- covariant forward and contravariant backward, and 'transpose' swaps the
-- two directions.  The dagger dualises the bimonoid laws — forward copy is
-- backward merge, forward discard is backward zero, and vice versa — and
-- that interlock is the missing lemma that makes 'Circuit.Net.mirrorNet'
-- total over a generic wiring tensor.
--
-- Design note: $copy-discard-design.
module Circuit.Bimonoid
  ( -- * Copy
    Copy (..),

    -- * Discard
    Discard (..),

    -- * Merge
    Merge (..),

    -- * Zero
    Zero (..),

    -- * Bundled synonyms
    CopyDiscard,
    MergeZero,
    Bimonoid,

    -- * Free-syntax signatures
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,

    -- * The substructural square
    Affine,
    Relevant,
    Cartesian,
    CoAffine,
    CoRelevant,

    -- * Tensor-generic capabilities
    CopyT (..),
    DiscardT (..),
    MergeT (..),
    ZeroT (..),
    BimonoidT,

    -- * Free dagger category
    Dagger (..),
    transpose,
  )
where

import Circuit.Category (Category (..))
import Circuit.Syntax (Algebra (..), (:+:) (..))
import Circuit.Tensor (Action (..), Tensor (..), Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Bimonoid
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Category (Category (..), (.>))
-- >>> import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Bimonoid
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Category (Category (..), (.>))
-- >>> import Prelude hiding (id, (.))

-- * Merge / Zero: monoid structure on channel objects

-- | Combine two values of the channel type.
--
-- Not the same as arithmetic '+'; this is the monoid operation by which
-- parallel contributions to the same wire combine.
class Merge arr a where
  plus :: arr (a, a) a

-- | The neutral element for 'plus'.
class Zero arr a where
  zero :: arr () a

-- | The bundled monoid class, retained as a synonym.
type MergeZero arr a = (Merge arr a, Zero arr a)

-- | The unit type carries the trivial monoid.
--
-- >>> plus ((), ()) :: ()
-- ()
-- >>> zero () :: ()
-- ()
instance Merge (->) () where
  plus _ = ()
  {-# INLINE plus #-}

instance Zero (->) () where
  zero _ = ()
  {-# INLINE zero #-}

-- | Numeric carriers.  'plus' is addition, 'zero' is 0.
--
-- >>> plus (1, 2) :: Int
-- 3
-- >>> zero () :: Int
-- 0
-- >>> plus (1.0, 2.0) :: Double
-- 3.0
-- >>> zero () :: Double
-- 0.0
instance Merge (->) Int where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Int where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Integer where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Integer where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Double where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Double where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Float where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Float where
  zero _ = 0
  {-# INLINE zero #-}

-- | Boolean monoid under disjunction.
--
-- Idempotent because @True || True = True@.
--
-- >>> plus (True, False) :: Bool
-- True
-- >>> zero () :: Bool
-- False
instance Merge (->) Bool where
  plus = uncurry (||)
  {-# INLINE plus #-}

instance Zero (->) Bool where
  zero _ = False
  {-# INLINE zero #-}

-- | Componentwise 'plus' on pairs.
--
-- >>> plus ((3, 4), (5, 6)) :: (Int, Int)
-- (8,10)
instance (Merge (->) a, Merge (->) b) => Merge (->) (a, b) where
  plus ((a, b), (a', b')) = (plus (a, a'), plus (b, b'))
  {-# INLINE plus #-}

instance (Zero (->) a, Zero (->) b) => Zero (->) (a, b) where
  zero u = (zero u, zero u)
  {-# INLINE zero #-}

-- | Lists via elementwise 'plus', padded with 'zero'.
--
-- For lists of unequal length, the shorter list is implicitly extended
-- with the element 'zero'. The unit is the empty list.
--
-- >>> plus ([1, 2], [3, 4, 5]) :: [Int]
-- [4,6,5]
-- >>> plus ([], [3, 4, 5]) :: [Int]
-- [3,4,5]
instance (Merge (->) a, Zero (->) a) => Merge (->) [a] where
  plus (xs, ys) = go xs ys
    where
      go [] [] = []
      go [] (y : ys') = plus (zero (), y) : go [] ys'
      go (x : xs') [] = plus (x, zero ()) : go xs' []
      go (x : xs') (y : ys') = plus (x, y) : go xs' ys'
  {-# INLINE plus #-}

instance Zero (->) [a] where
  zero _ = []
  {-# INLINE zero #-}

-- * Copy / Discard: comonoid structure on channel objects

-- | Copy a value into a pair.
--
-- Laws:
--
-- @
--   fst . copy = id              -- left unit
--   snd . copy = id              -- right unit
--   (copy × id) . copy = (id × copy) . copy  -- coassociativity
--   braid . copy = copy            -- cocommutativity
-- @
class Copy arr a where
  copy :: arr a (a, a)

-- | Discard a value.
class Discard arr a where
  discard :: arr a ()

-- | The bundled comonoid class, retained as a synonym.
type CopyDiscard arr a = (Copy arr a, Discard arr a)

-- | Both the comonoid and monoid on a channel object.
--
-- A constraint synonym — no instance required.  On a cartesian base arrow,
-- every type carries both structures.  This is the precondition for
-- 'Circuit.Net.mirrorNet' to be total on that base arrow.
type Bimonoid arr a = (Copy arr a, Discard arr a, Merge arr a, Zero arr a)

-- | Tensor-generic bimonoid: all four structural capabilities on the tensor.
--
-- This is the tensor-generic form of 'Bimonoid'.  It is the precondition for
-- 'Circuit.Net.mirrorNet' over a generic wiring tensor.
class (CopyT t arr a, DiscardT t arr a, MergeT t arr a, ZeroT t arr a) => BimonoidT t arr a

instance (CopyT t arr a, DiscardT t arr a, MergeT t arr a, ZeroT t arr a) => BimonoidT t arr a

-- * Tensor-generic capabilities

-- | Copy a value into the tensor product with itself.
--
-- This is the tensor-generic form of 'Copy'.  For the cartesian tensor
-- @(,)@ it reduces to @arr a (a, a)@ and the existing 'Copy' class is
-- recovered.  Other wiring tensors may supply their own instances.
class (Tensor t arr) => CopyT t arr a where
  copyT :: arr a (t a a)

-- | Discard a value to the tensor unit.
class (Tensor t arr) => DiscardT t arr a where
  discardT :: arr a (Unit t)

-- | Combine two values under the tensor product.
--
-- This is the tensor-generic form of 'Merge'. For the cartesian tensor
-- @(,)@ it reduces to @arr (a, a) a@ and the existing 'Merge' class is
-- recovered. Other wiring tensors may supply their own instances.
class (Tensor t arr) => MergeT t arr a where
  plusT :: arr (t a a) a

-- | The neutral element under the tensor product.
class (Tensor t arr) => ZeroT t arr a where
  zeroT :: arr (Unit t) a

-- * Free dagger category

-- The free dagger category itself — pairing a forward arrow with a backward
-- arrow and swapping them with 'transpose' — and the bimonoid interlock
-- instances that dualise the structural rules.

-- | The free dagger category over a base arrow.
--
-- @Dagger arr a b@ is a pair of arrows @arr a b@ (forward) and
-- @arr b a@ (backward).  Composition is covariant forward, contravariant
-- backward: @Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)@.
--
-- >>> let d = Dagger (+1) (subtract 1) :: Dagger (->) Int Int
-- >>> front d 5
-- 6
-- >>> back d 6
-- 5
data Dagger arr a b = Dagger
  { -- | The forward direction.
    front :: arr a b,
    -- | The backward direction.
    back :: arr b a
  }

-- | The dagger operation: braid forward and backward.
--
-- Involutive: @transpose . transpose = id@.
transpose :: Dagger arr a b -> Dagger arr b a
transpose (Dagger f g) = Dagger g f

instance (Category arr) => Category (Dagger arr) where
  id = Dagger id id
  {-# INLINE id #-}

  Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)
  {-# INLINE (.) #-}

instance (Strength t arr) => Strength t (Dagger arr) where
  strength (Dagger f g) = Dagger (strength f) (strength g)
  {-# INLINE strength #-}

instance (Yank t arr) => Yank t (Dagger arr) where
  yank (Dagger f g) = Dagger (yank f) (yank g)
  {-# INLINE yank #-}

-- | Forward copy, backward add — the bimonoid self-duality.
--
-- The interlock is the point to notice: 'Copy' on the dagger requires
-- 'Merge' on the base.  The comonoid and monoid cannot be granted
-- separately in this construction; @Dagger (FinRel k)@ is where that
-- collapse becomes observable (see the @circuits-axioma@ oracle).
instance (Copy arr a, Merge arr a) => Copy (Dagger arr) a where
  copy = Dagger copy plus
  {-# INLINE copy #-}

instance (Discard arr a, Zero arr a) => Discard (Dagger arr) a where
  discard = Dagger discard zero
  {-# INLINE discard #-}

-- | Forward add, backward copy.
instance (Merge arr a, Copy arr a) => Merge (Dagger arr) a where
  plus = Dagger plus copy
  {-# INLINE plus #-}

instance (Zero arr a, Discard arr a) => Zero (Dagger arr) a where
  zero = Dagger zero discard
  {-# INLINE zero #-}

-- | Tensor-generic bimonoid interlock through @Dagger@.
--
-- These instances mirror the cartesian ones above, but work for any wiring
-- tensor @t@.  They are the missing lemma that makes 'Circuit.Net.mirrorNet'
-- total: a 'Circuit.Net.Net' over 'Dagger arr' can transpose its bimonoid rows because
-- the dagger swaps the tensor-comonoid and tensor-monoid dictionaries.
--
-- The overlap with the default instances below at @CopyT (,) (Dagger arr) a@
-- is forced, not accidental: mirrorNet totality needs these instances for
-- every tensor @t@, and @t = (,)@ is also served by the OVERLAPPABLE
-- defaults.  It is coherent because both routes compute the same arrow —
-- the default route reduces @copy \@(Dagger arr)@ to @Dagger copy plus@ on
-- the base, which is exactly the body here.
--
-- The instances are INCOHERENT, and that is a load-bearing choice, not a
-- convenience: 'Circuit.Net.mirrorNet' re-emits the 'SigCopy'/'SigPlus'
-- rows at polymorphic types, so the goal @MergeT w (Dagger arr) a@ (and its
-- three siblings) must be resolved while @w@ and @arr@ are still type
-- variables — no specificity ordering between this head and the default's
-- head exists yet, and without INCOHERENT GHC reports the choice as
-- undecidable.  INCOHERENT makes GHC commit to the first matching instance
-- at such sites; since both routes compute the same arrow, the commitment
-- is safe.  The fragility to note: if a third instance ever enters either
-- chain, this commitment order becomes load-bearing for semantics, not just
-- totality.
--
-- >>> let d = copyT @(,) @(Dagger (->)) @Int :: Dagger (->) Int (Int, Int)
-- >>> front d 5
-- (5,5)
-- >>> back d (2, 3)
-- 5
instance {-# INCOHERENT #-} (CopyT t arr a, MergeT t arr a) => CopyT t (Dagger arr) a where
  copyT = Dagger (copyT @t) (plusT @t)
  {-# INLINE copyT #-}

instance {-# INCOHERENT #-} (DiscardT t arr a, ZeroT t arr a) => DiscardT t (Dagger arr) a where
  discardT = Dagger (discardT @t) (zeroT @t)
  {-# INLINE discardT #-}

instance {-# INCOHERENT #-} (MergeT t arr a, CopyT t arr a) => MergeT t (Dagger arr) a where
  plusT = Dagger (plusT @t) (copyT @t)
  {-# INLINE plusT #-}

instance {-# INCOHERENT #-} (ZeroT t arr a, DiscardT t arr a) => ZeroT t (Dagger arr) a where
  zeroT = Dagger (zeroT @t) (discardT @t)
  {-# INLINE zeroT #-}

instance (Unital t arr) => Unital t (Dagger arr) where
  unitl = Dagger unitl unitl'
  {-# INLINE unitl #-}
  unitl' = Dagger unitl' unitl
  {-# INLINE unitl' #-}
  unitr = Dagger unitr unitr'
  {-# INLINE unitr #-}
  unitr' = Dagger unitr' unitr
  {-# INLINE unitr' #-}

instance (Tensor t arr) => Tensor t (Dagger arr) where
  tensor (Dagger f g) (Dagger f' g') = Dagger (tensor f f') (tensor g g')
  {-# INLINE tensor #-}

instance (Action t arr) => Action t (Dagger arr) where
  braid = Dagger braid braid
  {-# INLINE braid #-}

instance (Assoc t arr) => Assoc t (Dagger arr) where
  assoc = Dagger assoc assoc'
  assoc' = Dagger assoc' assoc

instance (Slide t arr) => Slide t (Dagger arr) where
  slide = Dagger slide slide

-- * The substructural square

-- | Weakening without contraction: discard is available, copy is not.
--
-- One corner of the substructural square.  An 'Affine' base is one where a
-- morphism may silently drop its input.
type Affine arr a = Discard arr a

-- | Contraction without weakening: copy is available, discard is not.
type Relevant arr a = Copy arr a

-- | Both structural rules: the cartesian corner.
--
-- Same constraint set as 'CopyDiscard'; the name exists so the square reads
-- as a square.
type Cartesian arr a = (Copy arr a, Discard arr a)

-- | The ⅋-dual of 'Affine': the monoid unit is available, merge is not.
type CoAffine arr a = Zero arr a

-- | The ⅋-dual of 'Relevant': merge is available, the monoid unit is not.
--
-- The fourth corner — both 'Merge' and 'Zero' — is already named
-- 'MergeZero'.
type CoRelevant arr a = Merge arr a

-- $copy-discard-design
--
-- Copy/discard is not an ambient assumption on @(->)@.  The exponential
-- slice makes copying an explicit capability: a value of type @!A@ carries
-- a witness, and unmarked @A@ cannot be copied silently.
--
-- The instances below are the concrete copyable types used in the repo and
-- tests.  Adding a new copyable type requires an explicit instance rather
-- than a default structural rule.

-- | Unit trivially copies and discards.
--
-- >>> copy (() :: ())
-- ((),())
-- >>> discard (() :: ())
-- ()
instance Copy (->) () where
  copy u = (u, u)
  {-# INLINE copy #-}

instance Discard (->) () where
  discard _ = ()
  {-# INLINE discard #-}

-- | Numeric scalars copy and discard pointwise.
--
-- >>> copy (42 :: Int)
-- (42,42)
-- >>> discard (42 :: Int)
-- ()
instance Copy (->) Int where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Int where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Integer where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Integer where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Double where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Double where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Float where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Float where
  discard _ = ()
  {-# INLINE discard #-}

-- | Booleans copy and discard.
--
-- >>> copy True
-- (True,True)
-- >>> discard True
-- ()
instance Copy (->) Bool where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Bool where
  discard _ = ()
  {-# INLINE discard #-}

-- | Products copy and discard as a whole value.
instance Copy (->) (a, b) where
  copy ab = (ab, ab)
  {-# INLINE copy #-}

instance Discard (->) (a, b) where
  discard _ = ()
  {-# INLINE discard #-}

-- | Lists copy and discard as a whole value.
instance Copy (->) [a] where
  copy as = (as, as)
  {-# INLINE copy #-}

instance Discard (->) [a] where
  discard _ = ()
  {-# INLINE discard #-}

-- | Maybe copies and discards as a whole value.
instance Copy (->) (Maybe a) where
  copy m = (m, m)
  {-# INLINE copy #-}

instance Discard (->) (Maybe a) where
  discard _ = ()
  {-# INLINE discard #-}

-- * Free-syntax signatures for the bimonoid generators

-- | Copy: the contraction half of the comonoid.
--
-- The constructor carries a 'CopyT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigCopy (w :: Type -> Type -> Type) arr rec a b where
  SigCopy ::
    (CopyT w arr a) =>
    SigCopy w arr rec a (w a a)

instance Algebra (SigCopy w) arr arr' where
  type Ctx (SigCopy w) arr arr' = ()
  alg emb _ SigCopy = emb (copyT @w)

-- | Discard: the weakening half of the comonoid.
--
-- The constructor carries a 'DiscardT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigDiscard (w :: Type -> Type -> Type) arr rec a b where
  SigDiscard ::
    (DiscardT w arr a) =>
    SigDiscard w arr rec a (Unit w)

instance Algebra (SigDiscard w) arr arr' where
  type Ctx (SigDiscard w) arr arr' = ()
  alg emb _ SigDiscard = emb (discardT @w)

-- | Comonoid operations: copy and discard.
type SigCopyDiscard w = SigCopy w :+: SigDiscard w

-- | Plus: the multiplication half of the monoid.
--
-- The constructor carries a 'MergeT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigPlus (w :: Type -> Type -> Type) arr rec a b where
  SigPlus ::
    (MergeT w arr a) =>
    SigPlus w arr rec (w a a) a

instance Algebra (SigPlus w) arr arr' where
  type Ctx (SigPlus w) arr arr' = ()
  alg emb _ SigPlus = emb (plusT @w)

-- | Zero: the unit half of the monoid.
--
-- The constructor carries a 'ZeroT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigZero (w :: Type -> Type -> Type) arr rec a b where
  SigZero ::
    (ZeroT w arr a) =>
    SigZero w arr rec (Unit w) a

instance Algebra (SigZero w) arr arr' where
  type Ctx (SigZero w) arr arr' = ()
  alg emb _ SigZero = emb (zeroT @w)

-- | Monoid operations: plus and zero.
type SigMergeZero w = SigPlus w :+: SigZero w

-- * Default tensor-generic instances for the cartesian tensor

-- | Every 'Copy' instance gives a 'CopyT' instance for the cartesian tensor.
instance {-# OVERLAPPABLE #-} (Copy arr a, Tensor (,) arr) => CopyT (,) arr a where
  copyT = copy
  {-# INLINE copyT #-}

-- | Every 'Discard' instance gives a 'DiscardT' instance for the cartesian tensor.
instance {-# OVERLAPPABLE #-} (Discard arr a, Tensor (,) arr) => DiscardT (,) arr a where
  discardT = discard
  {-# INLINE discardT #-}

-- | Every 'Merge' instance gives a 'MergeT' instance for the cartesian tensor.
instance {-# OVERLAPPABLE #-} (Merge arr a, Tensor (,) arr) => MergeT (,) arr a where
  plusT = plus
  {-# INLINE plusT #-}

-- | The coproduct's merge is free for every object — the codiagonal,
-- uniform in a way the cartesian merge is not. This uniformity is the
-- coproduct fact the trace-to-iteration correspondence lives on:
-- @unfold g = yank (g . plusT)@ at 'Either', stated and cited in
-- "Circuit.Cell"'s 'Circuit.Cell.Unfold'.
--
-- >>> (plusT :: Either Int Int -> Int) (Left 3)
-- 3
-- >>> (plusT :: Either Int Int -> Int) (Right 3)
-- 3
instance MergeT Either (->) a where
  plusT = either id id
  {-# INLINE plusT #-}

-- | Every 'Zero' instance gives a 'ZeroT' instance for the cartesian tensor.
instance {-# OVERLAPPABLE #-} (Zero arr a, Tensor (,) arr) => ZeroT (,) arr a where
  zeroT = zero
  {-# INLINE zeroT #-}

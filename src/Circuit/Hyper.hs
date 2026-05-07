{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A Hyper is a Church encoding of a Circuit. The feedback channel is
-- structural in the type rather than explicit, so the sliding axiom
-- is inherent to composition rather than enforced by pattern matching.
--
-- Symbolic vocabulary:
--
--   * Type: @a ↬ b@ is a hyperfunction from @a@ to @b@.
--   * Invoke: @h ⇸ k@ applies hyperfunction @h@ to continuation @k@.
--   * Compose: @f ⊙ g@ is sequential composition (works for any 'Category').
--   * Push: @f ⊲ h@ prepends @f@ to hyperfunction @h@.
--   * Run: @(⥁) h@ ties the knot on the diagonal.

module Circuit.Hyper
  ( -- * Type
    Hyper (..),
    type (↬),

    -- * Core operations
    run,
    base,
    lift,
    push,

    -- * Interpretation
    lower,

    -- * Recursion combinators
    hyperAp,
    hyperBind,
    valueFix,
    hyperFix,

    -- * Coinductive helpers
    unroll,
    roll,
    ana,
    cata,

    -- * Symbolic operators
    (⇸),
    (⊙),
    (⊲),
    (⥁),
    (○),
    (↑),
    (↓),
  )
where

import Control.Category (Category (..), id)
import Data.Coerce (coerce)
import Data.Function (fix)
import Data.Profunctor (Profunctor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> {-# LANGUAGE PostfixOperators #-}
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Data.Function (fix)

-- | Hyper a b is a hyperfunction from a to b.
--
-- Defined as a function that invokes its own dual to produce a value.
-- The self-referential duality unifies the forward and backward directions
-- through a single continuation argument.
--
-- 
newtype Hyper a b = Hyper {invoke :: Hyper b a -> b}

-- | Infix type synonym for 'Hyper'.
--
-- >>> :type (undefined :: Int ↬ Int)
-- (undefined :: Int ↬ Int) :: Int ↬ Int
type (↬) = Hyper

instance {-# OVERLAPPING #-} Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- | Tie the knot on the diagonal: run a hyperfunction of type (a ↬ a) to get a value of type a.
--
-- This closes the feedback loop by invoking the hyperfunction with itself
-- repackaged as a continuation. The recursive definition:
--
-- > run h = invoke h (Hyper run)
--
-- creates the self-referential fixed point at the heart of coinductive hyperfunction semantics.
--
-- Non-termination is expected: @(+1)@ never reaches a fixed point.
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- | Lift a constant into a hyperfunction.
--
-- The resulting hyperfunction ignores its continuation and always returns the constant.
--
-- >>> lower (base 42) 0
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Infix synonym for 'base' (postfix constant).
--
-- >>> (42 ○) ↓ 0
-- 42
infixl 9 ○
(○) :: a -> Hyper b a
(○) = base

-- | Embed a plain function into a hyperfunction.
--
-- Defined recursively by prepending to itself:
--
-- > lift f = push f (lift f)
--
-- This unfolds the function application lazily, supporting arbitrary recursion depth.
--
-- >>> lower (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Postfix synonym for 'lift'.
--
-- >>> ((+1) ↑) ↓ 5
-- 6
infixr 9 ↑
(↑) :: (a -> b) -> Hyper a b
(↑) = lift

-- | Prepend a function to a hyperfunction (push in the stack).
--
-- This threads the continuation through the prepended function,
-- allowing feedback-aware composition of functions.
--
-- >>> lower ((+1) ⊲ lift (*2)) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Observe a hyperfunction by supplying it with a constant continuation.
--
-- This extracts a plain function from a hyperfunction by asking:
-- "what output do you produce when the feedback channel feeds back
-- the constant input a?"
--
-- >>> lower (lift reverse) "hello"
-- "olleh"
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (base a)

-- | Postfix synonym for 'lower'.
--
-- Because 'lower' returns a plain function, the postfix form
-- chains naturally via function application:
--
-- >>> ((+1) ↑) ↓ 5
-- 6
--
-- >>> ((*2) ↑) ↓ 5 + 10
-- 20
infixl 9 ↓
(↓) :: Hyper a b -> (a -> b)
(↓) = lower

-- ---------------------------------------------------------------------------
-- Coinductive helpers
-- ---------------------------------------------------------------------------

-- | Unroll a hyperfunction: expose the internal continuation-passing structure.
--
-- 'coerce' of 'invoke': @Hyper b a@ is representationally @Hyper a b -> a@.
unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll = coerce

-- | Roll a hyperfunction: repackage continuation-passing into a 'Hyper'.
roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = coerce

-- | Anamorphism: unfold a hyperfunction from a coalgebra.
--
-- @ana psi@ builds a 'Hyper' by threading state @x@ through @psi@,
-- which has access to the continuation via @invoke z . f@.
ana :: (x -> (x -> a) -> b) -> x -> Hyper a b
ana psi = f where f x = Hyper $ \z -> psi x (invoke z . f)

-- | Catamorphism: fold a hyperfunction down to a value.
--
-- From \"Generalizing the augment combinator\" by Ghani, Uustalu and Vene.
cata :: (((x -> a) -> b) -> x) -> Hyper a b -> x
cata phi = f where f h = phi $ \g -> unroll h (g . f)

-- ---------------------------------------------------------------------------
-- Typeclass instances
-- ---------------------------------------------------------------------------

-- While the type is nominally invariant in both parameters, coinductive
-- definitions (mutually recursive 'lmap'/'rmap', self-referential 'dimap')
-- make 'Profunctor', 'Functor', and 'Applicative' instances possible under
-- lazy evaluation, following the pattern from Kmett's hyperfunctions library.
-- 'Monad' is also possible (see Kmett) but omitted here for simplicity.
--
-- The combinators 'hyperAp' and 'hyperBind' serve as stand-alone equivalents
-- for applicative/monadic programming patterns that don't require instances.

-- | Profunctor via coinductive definitions.
--
-- 'dimap', 'lmap', and 'rmap' are mutually coinductive — they never
-- structurally terminate, relying on laziness to unfold on demand.
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

-- | Functor via 'rmap' from 'Profunctor'.
--
-- Despite @Hyper a@ being nominally invariant, the coinductive 'rmap'
-- (and therefore 'fmap') is sound under lazy evaluation.
instance Functor (Hyper a) where
  fmap = rmap

-- | Applicative via the coinductive anamorphism.
--
-- 'pure' is the same as 'base': a hyperfunction that ignores its continuation.
-- '(<*>)' uses 'ana' to thread two hyperfunctions in parallel.
instance Applicative (Hyper a) where
  pure = base
  p <* _ = p
  _ *> p = p
  (<*>) = curry $ ana $ \(i, j) fga ->
    unroll i (\i' -> fga (i', j)) $ unroll j (\j' -> fga (i, j'))

-- | Applicative-style application: feed the same input to a hyperfunction
-- of functions and a hyperfunction of values.
--
-- >>> hyperAp (lift ((+) . (3*))) (lift (2*)) ↓ 5
-- 25
hyperAp :: Hyper a (b -> c) -> Hyper a b -> Hyper a c
hyperAp hf hv = lift $ \a -> lower hf a (lower hv a)

-- | Monadic-style bind: sequence two hyperfunctions by threading the
-- output of the first into the second.
--
-- >>> (lift (+1) `hyperBind` \b -> lift (* b)) ↓ 5
-- 30
hyperBind :: Hyper a b -> (b -> Hyper a c) -> Hyper a c
hyperBind m k = lift $ \a -> lower (k (lower m a)) a

-- | Value-recursion: tie the knot at the output value for a fixed input.
--
-- >>> take 3 (lower (valueFix (\xs -> lift (\_ -> 1 : xs))) ())
-- [1,1,1]
valueFix :: (b -> Hyper a b) -> Hyper a b
valueFix f = lift $ \a -> fix $ \b -> lower (f b) a

-- | Structural recursion: tie the knot at the 'Hyper' level.
--
-- >>> lower (hyperFix (\f -> lift (\n -> if n == 0 then 1 else n * lower f (n - 1)))) 5
-- 120
hyperFix :: (Hyper a a -> Hyper a a) -> Hyper a a
hyperFix = fix

-- | Combine results pointwise via 'Semigroup'.
--
-- >>> (lift (:[]) <> lift (:[])) ↓ 5
-- [5,5]
instance Semigroup b => Semigroup (Hyper a b) where
  h1 <> h2 = lift $ \a -> lower h1 a <> lower h2 a

-- | Lift 'mempty' as a constant hyperfunction.
--
-- >>> lower (mempty :: Hyper () [Int]) ()
-- []
instance Monoid b => Monoid (Hyper a b) where
  mempty = base mempty

-- ---------------------------------------------------------------------------
-- Symbolic operators
-- ---------------------------------------------------------------------------

-- | Invoke a hyperfunction with a continuation.
--
-- Horizontal arrow with a vertical stroke — continuation-passing with
-- a pause / negative space.
--
-- >>> ((+1) ↑) ⇸ (0 ○)
-- 1
infixr 0 ⇸
(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

-- | Sequential composition. Polymorphic over any 'Category'.
--
-- >>> (((+1) ↑) ⊙ ((*2) ↑)) ↓ 5
-- 11
infixr 9 ⊙
(⊙) :: Category cat => cat b c -> cat a b -> cat a c
(⊙) = (.)

-- | Push / prepend a plain function to a hyperfunction.
--
-- >>> ((*2) ⊲ ((+1) ↑)) ↓ 5
-- 10
infixr 8 ⊲
(⊲) :: (a -> b) -> Hyper a b -> Hyper a b
(⊲) = push

-- | Tie the knot on the diagonal. Operator form of 'run'.
(⥁) :: Hyper a a -> a
(⥁) = run

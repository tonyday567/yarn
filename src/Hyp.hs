{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- |
-- Module      : HypH
-- Description : Hyperfunctions parameterised over a base arrow
--
-- @Hyp@ from Kidney & Wu is:
--
-- @
-- newtype a ↬ b = Hyp { ι :: (b ↬ a) → b }
-- @
--
-- which is @HypH (->) a b@. @HypH arr a b@ generalises the continuation
-- to any @Arrow arr@:
--
-- @
-- newtype HypH arr a b = HypH { ι :: arr (HypH arr b a) b }
-- @
--
-- = Why Arrow?
--
-- In @Hyp@, @⊙@ is:
--
-- @f ⊙ g = Hyp $ \h -> ι f (g ⊙ h)@
--
-- The @\h ->@ is free because @arr = (->)@. For @HypH arr@, the corecursion
-- @(g `zipper`) :: HypH arr c a -> HypH arr b a@ is a Haskell function that
-- needs lifting into @arr@. That requires @arr (g `zipper`)@, i.e. @Arrow arr@.
-- For @arr = MealyM@: @arr f = stateless f@ — a zero-state Mealy machine.
--
-- = Run
--
-- In @Hyp@: @run h = ι h (Hyp run)@ — @ι h@ is a function, applied directly.
--
-- For @HypH arr@, @ι h :: arr (HypH arr a a) a@ is an @arr@ morphism, not a
-- plain function. Applying it requires a driver, not a call. So @run@ does
-- not generalise uniformly:
--
-- * For @arr = (->)@: @runFn h = ι h (HypH runFn)@ recovers @Hyp.run@ exactly.
-- * For @arr = MealyM@: the ByteString driver IS @run@. There is no pure
--   @run :: HypH MealyM a a -> a@ — @MealyM@ needs inputs.
--
-- = The Rec {} problem
--
-- @Traced MealyM@ compiles via a recursive interpreter in @Rec {}@.
-- Inlining is blocked; composed state is a heap tuple per byte.
--
-- @HypH MealyM@ encodes the same structure corecursively. @zipper@ is
-- productive — each call unfolds one @ι f@ layer before recurring.
-- GHC sees plain @MealyM@ compositions with no recursive interpreter.
module Hyp
  ( HypH (..),

    -- * Core operations
    zipper,
    runFn,
    stream,

    -- * Producer / Consumer
    Producer,
    Consumer,
    Channel,
    prod,
    cons,

    -- * Co: coroutine over HypH
    Co (..),
    yield,
    send,
    send',

    -- * Examples
    zip,

    -- * Helpers
    base,
    rep,
    invoke,
  )
where

import Control.Arrow (Arrow (..))
import Control.Category (Category (..))
import Control.Monad.Cont
import Prelude hiding (id, zip, (.))

-- ---------------------------------------------------------------------------
-- The type
-- ---------------------------------------------------------------------------

-- | Hyperfunction over a base arrow @arr@.
--
-- @ι :: arr (HypH arr b a) b@
--
-- When @arr = (->)@: recovers @Hyp@ exactly.
-- When @arr = MealyM@: a Mealy machine whose input is the dual hyperfunction.
newtype HypH arr a b = HypH {ι :: arr (HypH arr b a) b}

-- ---------------------------------------------------------------------------
-- Core operations
-- ---------------------------------------------------------------------------

-- | Compose two @HypH arr@ morphisms. Recovers @Hyp@'s @(⊙)@.
--
-- @zipper f g = HypH $ ι f . arr (g `zipper`)@
--
-- Productive: unfolds @ι f@ before each recursive @zipper g h@.
-- Requires @Arrow arr@ to lift the Haskell corecursion into @arr@.
zipper :: (Arrow arr) => HypH arr b c -> HypH arr a b -> HypH arr a c
zipper f g = HypH $ ι f . arr (g `zipper`)

-- | Run a closed @HypH (->) a a@. Recovers @Hyp.run@.
runFn :: HypH (->) a a -> a
runFn h = ι h (HypH runFn)

-- | Stream cons. Recovers @Hyp@'s @(⊲)@.
stream :: (a -> b) -> HypH (->) a b -> HypH (->) a b
stream f h = HypH $ \k -> f (ι k h)

-- ---------------------------------------------------------------------------
-- Producer / Consumer / Channel
-- ---------------------------------------------------------------------------

type Producer arr o a = HypH arr (o -> a) a

type Consumer arr i a = HypH arr a (i -> a)

type Channel arr i o a = HypH arr (o -> a) (i -> a)

-- | Send a value through a producer. Recovers @Hyp.prod@.
prod :: o -> Producer (->) o a -> Producer (->) o a
prod o p = HypH $ \q -> ι q p o

-- | Prepend a receipt step to a consumer. Recovers @Hyp.cons@.
cons :: (i -> a -> a) -> Consumer (->) i a -> Consumer (->) i a
cons f p = HypH $ \q -> \i -> f i (ι q p)

-- ---------------------------------------------------------------------------
-- Co: coroutine over HypH (->) — recovers Hyp's Co
-- ---------------------------------------------------------------------------

-- | Coroutine: a function from a continuation to a channel.
-- Identical structure to @Hyp.Co@ with @(↬)@ replaced by @HypH (->)@.
newtype Co r i o m a = Co
  {route :: (a -> Channel (->) i o (m r)) -> Channel (->) i o (m r)}

-- | Yield a value, await a response. Recovers @Hyp.yield@.
yield :: o -> Co r i o m i
yield x = Co $ \k -> HypH $ \h i -> invoke h (k i) x

-- | Send a value into a coroutine. Recovers @Hyp.send@.
send ::
  (MonadCont m) =>
  Co r i o m r ->
  i ->
  m (Either r (o, Co r i o m r))
send c v = callCC $ \k ->
  Left
    <$> invoke
      (route c (\x -> HypH (\_ _ -> return x)))
      (HypH (\r o -> k (Right (o, Co (const r)))))
      v

-- | Send, assuming no termination. Recovers @Hyp.send'@.
send' :: (MonadCont m) => Co x i o m x -> i -> m (o, Co x i o m x)
send' c v = either undefined id <$> send c v

-- ---------------------------------------------------------------------------
-- Examples
-- ---------------------------------------------------------------------------

-- | Zip two lists using hyperfunctions and foldr. Recovers @Hyp.zip@.
--
-- Two @foldr@s connected by @invoke@. No index, no accumulator.
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = ι (foldr xf xb xs) (foldr yf yb ys)
  where
    xf :: a -> Producer (->) a [(a, b)] -> Producer (->) a [(a, b)]
    xf x xk = prod x xk

    xb :: Producer (->) a [(a, b)]
    xb = HypH $ \_ -> []

    yf :: b -> Consumer (->) a [(a, b)] -> Consumer (->) a [(a, b)]
    yf y yk = cons (\x xys -> (x, y) : xys) yk

    yb :: Consumer (->) a [(a, b)]
    yb = HypH $ \_ _ -> []

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Terminal: ignore continuation, return @a@. Recovers @Hyp.base@.
base :: a -> HypH (->) a a
base a = HypH (const a)

-- | Repeat a function forever. Recovers @Hyp.rep@.
rep :: (a -> b) -> HypH (->) a b
rep f = stream f (rep f)

-- | Invoke @f@ against @g@. Recovers @Hyp.invoke@.
invoke :: HypH (->) a b -> HypH (->) b a -> b
invoke f g = runFn (zipper f g)

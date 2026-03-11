{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- |
-- Module      : Hyp
-- Description : Hyperfunctions parameterised over a base arrow
--
-- Reference: Kidney & Wu, "Hyperfunctions: Communicating Continuations"
-- (<https://doisinkidney.com/posts/2025-11-18-hyperfunctions.html>), to be published at POPL 2026.
--
-- @Hyp@ from Kidney & Wu is:
--
-- @
-- newtype a ↬ b = Hyp { ι :: (b ↬ a) → b }
-- @
--
-- which is @Hyp (->) a b@. @Hyp arr a b@ generalises the continuation
-- to any @Arrow arr@:
--
-- @
-- newtype Hyp arr a b = Hyp { ι :: arr (Hyp arr b a) b }
-- @
--
-- = Why Arrow?
--
-- In @Hyp@, @⊙@ is:
--
-- @f ⊙ g = Hyp $ \h -> ι f (g ⊙ h)@
--
-- The @\h ->@ is free because @arr = (->)@. For @Hyp arr@, the corecursion
-- @(g `zipper`) :: Hyp arr c a -> Hyp arr b a@ is a Haskell function that
-- needs lifting into @arr@. That requires @arr (g `zipper`)@, i.e. @Arrow arr@.
-- For @arr = MealyM@: @arr f = stateless f@ — a zero-state Mealy machine.
--
-- = Run
--
-- In @Hyp@: @run h = ι h (Hyp run)@ — @ι h@ is a function, applied directly.
--
-- For @Hyp arr@, @ι h :: arr (Hyp arr a a) a@ is an @arr@ morphism, not a
-- plain function. Applying it requires a driver, not a call. So @run@ does
-- not generalise uniformly:
--
-- * For @arr = (->)@: @runFn h = ι h (Hyp runFn)@ recovers @Hyp.run@ exactly.
-- * For @arr = MealyM@: the ByteString driver IS @run@. There is no pure
--   @run :: Hyp MealyM a a -> a@ — @MealyM@ needs inputs.
--
-- = The Rec {} problem
--
-- @Traced MealyM@ compiles via a recursive interpreter in @Rec {}@.
-- Inlining is blocked; composed state is a heap tuple per byte.
--
-- @Hyp MealyM@ encodes the same structure corecursively. @zipper@ is
-- productive — each call unfolds one @ι f@ layer before recurring.
-- GHC sees plain @MealyM@ compositions with no recursive interpreter.
module Hyp
  ( Hyp (..),
    type (↬),

    -- * Core operations
    zipper,
    run,
    runFn,
    stream,
    (⊲),
    (⊙),

    -- * Producer / Consumer
    Producer,
    Consumer,
    Channel,
    prod,
    cons,

    -- * Co: coroutine over Hyp
    Co (..),
    yield,
    send,
    send',

    -- * Bridge from Traced
    toHyp,
    fromHyp,
    toHypF,
    closeHyp,
    runHypWu,
    traceHypWu,

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
import Traced qualified

-- ---------------------------------------------------------------------------
-- The type
-- ---------------------------------------------------------------------------

-- | Hyperfunction over a base arrow @arr@.
--
-- @ι :: arr (Hyp arr b a) b@
--
-- When @arr = (->)@: recovers @Hyp@ exactly.
-- When @arr = MealyM@: a Mealy machine whose input is the dual hyperfunction.
newtype Hyp arr a b = Hyp {ι :: arr (Hyp arr b a) b}

-- ---------------------------------------------------------------------------
-- Specialization to (->)
-- ---------------------------------------------------------------------------

-- | Type alias: @a ↬ b@ = @Hyp (->) a b@
-- Recovers the Kidney & Wu notation for hyperfunctions over functions.
type a ↬ b = Hyp (->) a b

-- | Stream constructor: prepend a function to a hyperfunction.
--
-- @(⊲) :: (a -> b) -> (a ↬ b) -> (a ↬ b)@
-- 
-- Specialized from @stream@.
(⊲) :: (a -> b) -> (a ↬ b) -> (a ↬ b)
f ⊲ h = Hyp (\k -> f (ι k h))

-- | Composition: sequential combination of hyperfunctions.
--
-- @(⊙) :: (b ↬ c) -> (a ↬ b) -> (a ↬ c)@
--
-- Specialized from @zipper@.
(⊙) :: (b ↬ c) -> (a ↬ b) -> (a ↬ c)
f ⊙ g = Hyp $ \h -> ι f (g ⊙ h)

-- ---------------------------------------------------------------------------
-- Core operations
-- ---------------------------------------------------------------------------

-- | Compose two @Hyp arr@ morphisms. Recovers @Hyp@'s @(⊙)@.
--
-- @zipper f g = Hyp $ ι f . arr (g `zipper`)@
--
-- Productive: unfolds @ι f@ before each recursive @zipper g h@.
-- Requires @Arrow arr@ to lift the Haskell corecursion into @arr@.
zipper :: (Arrow arr) => Hyp arr b c -> Hyp arr a b -> Hyp arr a c
zipper f g = Hyp $ ι f . arr (g `zipper`)

-- | Run a closed hyperfunction to a value (Kidney & Wu style).
-- 
-- Ties the knot by invoking the hyperfunction against itself.
-- Only works for @arr = (->)@ because we need to actually apply the morphism.
run :: Hyp (->) a a -> a
run h = ι h (Hyp run)

-- | Alias for @run@. Emphasizes function specialization.
runFn :: Hyp (->) a a -> a
runFn = run

-- | Stream cons. Recovers @Hyp@'s @(⊲)@.
stream :: (a -> b) -> Hyp (->) a b -> Hyp (->) a b
stream f h = Hyp $ \k -> f (ι k h)

-- ---------------------------------------------------------------------------
-- Producer / Consumer / Channel
-- ---------------------------------------------------------------------------

type Producer arr o a = Hyp arr (o -> a) a

type Consumer arr i a = Hyp arr a (i -> a)

type Channel arr i o a = Hyp arr (o -> a) (i -> a)

-- | Send a value through a producer. Recovers @Hyp.prod@.
prod :: o -> Producer (->) o a -> Producer (->) o a
prod o p = Hyp $ \q -> ι q p o

-- | Prepend a receipt step to a consumer. Recovers @Hyp.cons@.
cons :: (i -> a -> a) -> Consumer (->) i a -> Consumer (->) i a
cons f p = Hyp $ \q -> \i -> f i (ι q p)

-- ---------------------------------------------------------------------------
-- Co: coroutine over Hyp (->) — recovers Hyp's Co
-- ---------------------------------------------------------------------------

-- | Coroutine: a function from a continuation to a channel.
-- Identical structure to @Hyp.Co@ with @(↬)@ replaced by @Hyp (->)@.
newtype Co r i o m a = Co
  {route :: (a -> Channel (->) i o (m r)) -> Channel (->) i o (m r)}

-- | Yield a value, await a response. Recovers @Hyp.yield@.
yield :: o -> Co r i o m i
yield x = Co $ \k -> Hyp $ \h i -> invoke h (k i) x

-- | Send a value into a coroutine. Recovers @Hyp.send@.
send ::
  (MonadCont m) =>
  Co r i o m r ->
  i ->
  m (Either r (o, Co r i o m r))
send c v = callCC $ \k ->
  Left
    <$> invoke
      (route c (\x -> Hyp (\_ _ -> return x)))
      (Hyp (\r o -> k (Right (o, Co (const r)))))
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
    xb = Hyp $ \_ -> []

    yf :: b -> Consumer (->) a [(a, b)] -> Consumer (->) a [(a, b)]
    yf y yk = cons (\x xys -> (x, y) : xys) yk

    yb :: Consumer (->) a [(a, b)]
    yb = Hyp $ \_ _ -> []

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Terminal: ignore continuation, return @a@. Recovers @Hyp.base@.
base :: a -> Hyp (->) a a
base a = Hyp (const a)

-- | Repeat a function forever. Recovers @Hyp.rep@.
rep :: (a -> b) -> Hyp (->) a b
rep f = stream f (rep f)

-- | Invoke @f@ against @g@. Recovers @Hyp.invoke@.
invoke :: Hyp (->) a b -> Hyp (->) b a -> b
invoke f g = runFn (zipper f g)

-- ---------------------------------------------------------------------------
-- Bridges from Traced
-- ---------------------------------------------------------------------------

-- | Catamorphism: fold @Traced (->)@ into @Hyp (->)@.
--
-- This is the fugal extension (Boccali et al., "Bicategories of Automata").
-- Every @Traced (->)@ description has a canonical corecursive unfolding into
-- @Hyp (->)@. Feedback is handled by @zipper@ rather than a lazy fixed point
-- — the recursion lives in the types, not in a @fix@ call.
--
-- @
-- Pure     →  rep id          — stateless identity, repeated
-- Lift f   →  rep f           — stateless f, repeated
-- Compose  →  zipper          — productive sequential composition
-- Loop p   →  closeHyp        — close feedback wire corecursively
-- @
--
-- Contrast with @toHypWu@: that collapses @Loop@ via @runFn@ (a lazy fixed
-- point). @toHyp@ preserves the loop structure corecursively in the tower.
toHyp :: Traced.Traced (->) a b -> Hyp (->) a b
toHyp Traced.Pure = rep id
toHyp (Traced.Lift f) = rep f
toHyp (Traced.Compose g h) = toHyp g `zipper` toHyp h
toHyp (Traced.Loop p) = closeHyp (toHyp p)

-- | Close a @Hyp (->)@ feedback loop.
--
-- @Hyp (->) (a, c) (b, c)  →  Hyp (->) a b@
--
-- The @c@ output wire feeds back as @c@ input corecursively.
-- The lazy fixed point ties @c@ inside the hyperfunction tower.
-- For productive @c@ (lazy structures), no @fix@ is needed in the caller.
closeHyp :: Hyp (->) (a, c) (b, c) -> Hyp (->) a b
closeHyp p = Hyp $ \k ->
  let (b, _) = ι p dual
      dual = Hyp $ \_ -> (ι k (closeHyp p), snd (ι p dual))
   in b

-- | Inverse of @toHyp@: unfold @Hyp (->)@ back to @Traced@ syntax.
--
-- Supplies the terminal continuation to collapse one tower layer,
-- returning a @Traced@ that lifts the result.
fromHyp :: Hyp (->) a b -> Traced.Traced (->) a b
fromHyp h = Traced.Lift $ \a -> ι h (Hyp (const a))

-- | Interpret @Traced@ parameterized by hyperfunctions into hyperfunctions.
--
-- This is an alternative bridge: whereas @toHyp@ and @toHypF@ interpret 
-- @Traced (->)@ (Traced over plain functions), @runHypWu@ interprets 
-- @Traced (Hyp (->))@ (Traced where the arrow itself is hyperfunctions).
--
-- This represents a second-order structure: feedback over hyperfunctions.
-- Currently unused but architecturally interesting.
runHypWu :: Traced.Traced (Hyp (->)) a b -> Hyp (->) a b
runHypWu Traced.Pure = rep id
runHypWu (Traced.Lift h) = h
runHypWu (Traced.Compose g h) = runHypWu g ⊙ runHypWu h
runHypWu (Traced.Loop p) = traceHypWu (runHypWu p)

-- | Tie feedback knot in a hyperfunction via lazy fixed point.
--
-- Takes a hyperfunction with feedback channel @c@ and closes it by computing
-- the fixed point with @c@ as both input and output.
--
-- @(a, c) ↬ (b, c)  →  a ↬ b@
--
-- The fixed point is computed eagerly using Haskell's lazy evaluation;
-- used by @runHypWu@ to discharge @Loop@.
traceHypWu :: (a, c) ↬ (b, c) -> Hyp (->) a b
traceHypWu h = rep $ \a ->
  fst $ fix $ \(_, c) -> ι h (Hyp (const (a, c)))
  where
    fix f = let x = f x in x

-- | Alternative bridge: @Traced@ to @Hyp (->)@ via eager fixed point.
--
-- Unlike @toHyp@ which preserves @Loop@ in the hyperfunction tower,
-- @toHypF@ collapses @Loop@ immediately using @run@, computing
-- the fixed point eagerly and lifting the result into hyperfunction.
toHypF :: Traced.Traced (->) a b -> Hyp (->) a b
toHypF Traced.Pure = rep id
toHypF (Traced.Lift f) = rep f
toHypF (Traced.Compose g h) = toHypF g `zipper` toHypF h
toHypF u@(Traced.Loop _) = rep (Traced.runFn u)

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

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

import Control.Arrow (Arrow, arr)
import Control.Category (Category (..))
import Control.Monad.Cont
import Prelude hiding (id, zip, (.))
import Traced qualified

-- | Hyperfunction over a base arrow @arr@.
newtype Hyp arr a b = Hyp {ι :: arr (Hyp arr b a) b}

-- | Type alias: @a ↬ b@ = @Hyp (->) a b@
type a ↬ b = Hyp (->) a b

-- | Stream constructor: prepend a function to a hyperfunction.
(⊲) :: (a -> b) -> (a ↬ b) -> (a ↬ b)
f ⊲ h = Hyp (\k -> f (ι k h))

-- | Composition: sequential combination of hyperfunctions.
(⊙) :: (b ↬ c) -> (a ↬ b) -> (a ↬ c)
f ⊙ g = Hyp $ \h -> ι f (g ⊙ h)

-- | Compose two @Hyp arr@ morphisms.
zipper :: (Arrow arr) => Hyp arr b c -> Hyp arr a b -> Hyp arr a c
zipper f g =  Hyp (ι f . arr (g `zipper`))

-- | Run a closed hyperfunction to a value.
run :: Hyp (->) a a -> a
run h = ι h (Hyp run)

-- | Alias for @run@.
runFn :: Hyp (->) a a -> a
runFn = run

-- | Stream cons.
stream :: (a -> b) -> Hyp (->) a b -> Hyp (->) a b
stream f h = Hyp $ \k -> f (ι k h)

type Producer arr o a = Hyp arr (o -> a) a

type Consumer arr i a = Hyp arr a (i -> a)

type Channel arr i o a = Hyp arr (o -> a) (i -> a)

-- | Send a value through a producer.
prod :: o -> Producer (->) o a -> Producer (->) o a
prod o p = Hyp $ \q -> ι q p o

-- | Prepend a receipt step to a consumer.
cons :: (i -> a -> a) -> Consumer (->) i a -> Consumer (->) i a
cons f p = Hyp $ \q -> \i -> f i (ι q p)

-- | Coroutine: a function from a continuation to a channel.
newtype Co r i o m a = Co
  {route :: (a -> Channel (->) i o (m r)) -> Channel (->) i o (m r)}

-- | Yield a value, await a response.
yield :: o -> Co r i o m i
yield x = Co $ \k -> Hyp $ \h i -> ι h (k i) x

-- | Send a value into a coroutine.
send ::
  (MonadCont m) =>
  Co r i o m r ->
  i ->
  m (Either r (o, Co r i o m r))
send c v = callCC $ \k ->
  Left
    <$> ι
      (route c (\x -> Hyp (\_ _ -> return x)))
      (Hyp (\r o -> k (Right (o, Co (const r)))))
      v

-- | Send, assuming no termination.
send' :: (MonadCont m) => Co x i o m x -> i -> m (o, Co x i o m x)
send' c v = either undefined id <$> send c v

-- | Zip two lists using hyperfunctions and foldr.
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

-- | Terminal: ignore continuation, return @a@.
base :: a -> Hyp (->) a a
base a = Hyp (const a)

-- | Repeat a function forever.
rep :: (a -> b) -> Hyp (->) a b
rep f = stream f (rep f)

-- | Invoke @f@ against @g@.
invoke :: Hyp (->) a b -> Hyp (->) b a -> b
invoke f g = run (zipper f g)

-- | Close a @Hyp@ feedback loop.
closeHyp :: Hyp (->) (a, c) (b, c) -> Hyp (->) a b
closeHyp p = Hyp $ \k ->
  let (b, _) = ι p dual
      dual = Hyp $ \_ -> (ι k (closeHyp p), snd (ι p dual))
  in b

-- | Unfold @Hyp@ back to @Traced@ syntax.
fromHyp :: Hyp (->) a b -> Traced.Traced (->) a b
fromHyp h = Traced.Lift $ \a -> ι h (Hyp (const a))

-- | Interpret @Traced@ parameterized by hyperfunctions into hyperfunctions.
runHypWu :: Traced.Traced (Hyp (->)) a b -> Hyp (->) a b
runHypWu Traced.Pure = rep id
runHypWu (Traced.Lift h) = h
runHypWu (Traced.Compose g h) = runHypWu g ⊙ runHypWu h
runHypWu (Traced.Knot p) = traceHypWu (runHypWu p)

-- | Tie feedback knot in a hyperfunction via lazy fixed point.
traceHypWu :: (a, c) ↬ (b, c) -> Hyp (->) a b
traceHypWu h = rep $ \a ->
  fst $ fix $ \(_, c) -> ι h (Hyp (const (a, c)))
  where
    fix f = let x = f x in x

-- | Alternative bridge: @Traced@ to @Hyp (->)@ via eager fixed point.
toHypF :: Traced.Traced (->) a b -> Hyp (->) a b
toHypF Traced.Pure = rep id
toHypF (Traced.Lift f) = rep f
toHypF (Traced.Compose g h) = toHypF g `zipper` toHypF h
toHypF u@(Traced.Knot _) = rep (Traced.run u)


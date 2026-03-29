{-# LANGUAGE RankNTypes #-}

-- | Producer, Consumer, Channel patterns and coroutines
module Hyp.Channel
  ( Producer,
    Consumer,
    Channel,
    prod,
    cons,
    Co (..),
    yield,
    send,
    send',
    zip,
  )
where

import Control.Monad.Cont
import Data.Function (fix)
import Prelude hiding (zip, (.))
import Hyp (HypA (..), Hyp)

type Producer o a = Hyp (o -> a) a

type Consumer i a = Hyp a (i -> a)

type Channel i o a = Hyp (o -> a) (i -> a)

-- | Send a value through a producer.
prod :: o -> Producer o a -> Producer o a
prod o p = HypA $ \q -> ι q p o

-- | Prepend a receipt step to a consumer.
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = HypA $ \q -> \i -> f i (ι q p)

-- | Coroutine: a function from a continuation to a channel.
newtype Co r i o m a = Co
  {route :: (a -> Channel i o (m r)) -> Channel i o (m r)}

-- | Yield a value, await a response.
yield :: o -> Co r i o m i
yield x = Co $ \k -> HypA $ \h i -> ι h (k i) x

-- | Send a value into a coroutine.
send ::
  (MonadCont m) =>
  Co r i o m r ->
  i ->
  m (Either r (o, Co r i o m r))
send c v = callCC $ \k ->
  Left
    <$> ι
      (route c (\x -> HypA (\_ _ -> return x)))
      (HypA (\r o -> k (Right (o, Co (const r)))))
      v

-- | Send, assuming no termination.
send' :: (MonadCont m) => Co x i o m x -> i -> m (o, Co x i o m x)
send' c v = either undefined id <$> send c v

-- | Zip two lists using hyperfunctions and foldr.
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = ι (foldr xf xb xs) (foldr yf yb ys)
  where
    xf :: a -> Producer a [(a, b)] -> Producer a [(a, b)]
    xf x xk = prod x xk

    xb :: Producer a [(a, b)]
    xb = HypA $ \_ -> []

    yf :: b -> Consumer a [(a, b)] -> Consumer a [(a, b)]
    yf y yk = cons (\x xys -> (x, y) : xys) yk

    yb :: Consumer a [(a, b)]
    yb = HypA $ \_ _ -> []

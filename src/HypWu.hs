{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- \* hyperfunctions (Kidney & Wu original)
-- "Hyperfunctions: Communicating Continuations" by Donnacha Oisín Kidney and Nicolas Wu, to be published at POPL 2026 Doisinkidney.
-- The preprint is available at: https://doisinkidney.com/posts/2025-11-18-hyperfunctions.html
module HypWu where

-- import Data.These (These(..))
-- import Data.Map.Strict (Map)
-- import Control.Monad.State (State)
-- import Control.Applicative
-- import Text.Regex.Applicative qualified as RE
-- import Text.Regex.Applicative (RE(..))
-- import Data.Char (chr)
import Control.Monad.Cont
import Prelude hiding (zip)

-- Core hyperfunction type
newtype a ↬ b = Hyp {ι :: (b ↬ a) -> b}

-- Stream constructor
(⊲) :: (a -> b) -> (a ↬ b) -> (a ↬ b)
f ⊲ h = Hyp (\k -> f (ι k h))

-- Zipper
(⊙) :: (b ↬ c) -> (a ↬ b) -> (a ↬ c)
f ⊙ g = Hyp $ \h -> ι f (g ⊙ h)

-- Runner
run :: a ↬ a -> a
run h = ι h (Hyp run)

-- Producer/Consumer
type Producer o a = (o -> a) ↬ a

type Consumer i a = a ↬ (i -> a)

type Channel a i o = (o -> a) ↬ (i -> a)

-- Producer and Consumer helpers
-- prod sends a value through a producer
-- ι (prod o p) q = ι q p o
prod :: o -> Producer o a -> Producer o a
prod o p = Hyp $ \q -> ι q p o

-- cons sends a consumer function through a consumer
-- ι (cons f p) q i = f i (ι q p)
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyp $ \q -> \i -> f i (ι q p)

newtype Co r i o m a = Co {route :: (a -> Channel (m r) i o) -> Channel (m r) i o}

yield :: o -> Co r i o m i
yield x = Co (\k -> Hyp (\h i -> invoke h (k i) x))

send :: (MonadCont m) => Co r i o m r -> i -> m (Either r (o, Co r i o m r))
send c v = callCC $ \k -> Left <$> invoke (route c (\x -> Hyp (\_ _ -> return x))) (Hyp (\r o -> k (Right (o, Co (const r))))) v

send' :: (MonadCont m) => Co x i o m x -> i -> m (o, Co x i o m x)
send' c v = either undefined id <$> send c v

-- Zip using hyperfunctions and foldr
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = ι (foldr xf xb xs) (foldr yf yb ys)
  where
    xf :: a -> Producer a [(a, b)] -> Producer a [(a, b)]
    xf x xk = prod x xk

    xb :: Producer a [(a, b)]
    xb = Hyp $ \_ -> []

    yf :: b -> Consumer a [(a, b)] -> Consumer a [(a, b)]
    yf y yk = cons (\x xys -> (x, y) : xys) yk

    yb :: Consumer a [(a, b)]
    yb = Hyp $ \_ _ -> []

-- Construction helpers
base :: a -> (a ↬ a)
base a = Hyp (const a)

rep :: (a -> b) -> (a ↬ b)
rep ab = ab ⊲ rep ab

-- Composition helper
--
-- >> ι f g = run (f ⊙ g)
invoke :: (a ↬ b) -> (b ↬ a) -> b
invoke f g = run (f ⊙ g)

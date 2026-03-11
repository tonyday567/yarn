{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
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
import Traced qualified
import Hyp qualified
import Hyp ((⊲), (⊙))

-- Core hyperfunction type: use Hyp's implementation
type a ↬ b = Hyp.Hyp (->) a b

-- Constructor pattern: accept either Hyp or bare lambda
pattern Hyp :: (Hyp.Hyp (->) b a -> b) -> (a ↬ b)
pattern Hyp f = Hyp.Hyp f

-- Runner
run :: a ↬ a -> a
run h = Hyp.ι h (Hyp run)

-- Producer/Consumer
type Producer o a = (o -> a) ↬ a

type Consumer i a = a ↬ (i -> a)

type Channel a i o = (o -> a) ↬ (i -> a)

-- Producer and Consumer helpers
-- prod sends a value through a producer
-- Hyp.ι (prod o p) q = Hyp.ι q p o
prod :: o -> Producer o a -> Producer o a
prod o p = Hyp $ \q -> Hyp.ι q p o

-- cons sends a consumer function through a consumer
-- Hyp.ι (cons f p) q i = f i (Hyp.ι q p)
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyp $ \q -> \i -> f i (Hyp.ι q p)

newtype Co r i o m a = Co {route :: (a -> Channel (m r) i o) -> Channel (m r) i o}

yield :: o -> Co r i o m i
yield x = Co (\k -> Hyp (\h i -> invoke h (k i) x))

send :: (MonadCont m) => Co r i o m r -> i -> m (Either r (o, Co r i o m r))
send c v = callCC $ \k -> Left <$> invoke (route c (\x -> Hyp (\_ _ -> return x))) (Hyp (\r o -> k (Right (o, Co (const r))))) v

send' :: (MonadCont m) => Co x i o m x -> i -> m (o, Co x i o m x)
send' c v = either undefined id <$> send c v

-- Zip using hyperfunctions and foldr
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = Hyp.ι (foldr xf xb xs) (foldr yf yb ys)
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

-- ---------------------------------------------------------------------------
-- Bridges from Traced
-- ---------------------------------------------------------------------------

-- | Interpret @Traced (↬)@ into @Hyp@.
runHypWu :: Traced.Traced (Hyp.Hyp (->)) a b -> (a ↬ b)
runHypWu Traced.Pure = rep id
runHypWu (Traced.Lift h) = h
runHypWu (Traced.Compose g h) = runHypWu g ⊙ runHypWu h
runHypWu (Traced.Loop p) = traceHypWu (runHypWu p)

-- | Close a hyperfunction feedback loop.
--
-- @(a, c) ↬ (b, c)  →  a ↬ b@
--
-- Evaluate with the terminal continuation, take the Haskell fixed point
-- over the @c@ channel.
traceHypWu :: (a, c) ↬ (b, c) -> (a ↬ b)
traceHypWu h = rep $ \a ->
  fst $ fix $ \(_, c) -> Hyp.ι h (Hyp (const (a, c)))
  where
    fix f = let x = f x in x

-- | Catamorphism: fold @Traced (->)@ into @Hyp@.
--
-- Initial algebra → final coalgebra.
-- Same object, different notation, different side of the erasure line.
toHypWu :: Traced.Traced (->) a b -> (a ↬ b)
toHypWu Traced.Pure = rep id
toHypWu (Traced.Lift f) = rep f
toHypWu (Traced.Compose g h) = toHypWu g ⊙ toHypWu h
toHypWu u@(Traced.Loop _) = rep (Traced.runFn u)

-- | Depth-1 unfolding: @Hyp@ → @Traced (->)@.
--
-- Supply the terminal continuation @Hyp (const a)@ to collapse the tower.
fromHypWu :: (a ↬ b) -> Traced.Traced (->) a b
fromHypWu h = Traced.Lift $ \a -> Hyp.ι h (Hyp (const a))

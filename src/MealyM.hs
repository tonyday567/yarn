{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UnicodeSyntax #-}

-- |
-- Module      : MealyM
-- Description : Pure Mealy machine, base category for Traced
--
-- MealyM a b  =  exists s. (s, s -> a -> (b, s))
--                           initial   transition
--
-- Fixed initial state, output on every step.
--
-- Contrast with the statistics Mealy (fold encoding):
--   Mealy a b  =  exists s. (a -> s, s -> a -> s, s -> b)
-- The fold encoding initialises state from the first element.
-- The machine encoding has a fixed start state — right for Traced.
--
-- Composition: state is the product, right runs first.
-- All pairing happens at construction time, not per-input.
--
-- ArrowLoop: sequential feedback.
-- loop m where m :: MealyM (a,c) (b,c)
--   state = (s, c)       machine state paired with previous feedback value
--   step  = c from step n is input c at step n+1  (one-step delay)
-- Initial c is undefined but never forced for well-formed machines.
--
-- Use with Traced:
--   run :: Traced MealyM a b -> MealyM a b
-- Compiles a composed machine description to one state machine.
-- Product state computed at construction time, no allocation per input.

module MealyM
  ( MealyM (..)
  , mkMealy
  , drive
  , driveList
  , stepList
  , stateless
  , withState
  , accum
  , count
  , latch
  ) where

import Prelude hiding (id, (.))
import qualified Prelude

import Control.Category (Category (..))
import Control.Arrow    (Arrow (..), ArrowLoop (..))
import Data.Profunctor  (Profunctor (..), Strong (..))

-- | Mealy machine with existential state.
data MealyM a b = forall s. MealyM s (s -> a -> (b, s))

mkMealy :: s -> (s -> a -> (b, s)) -> MealyM a b
mkMealy = MealyM

instance Category MealyM where
  id = MealyM () (\() a -> (a, ()))
  MealyM sf f . MealyM sg g = MealyM (sf, sg) step
    where
      step (s, t) a =
        let (mid, t') = g t a
            (out, s') = f s mid
        in  (out, (s', t'))

instance Arrow MealyM where
  arr f = MealyM () (\() a -> (f a, ()))
  first (MealyM s0 f) = MealyM s0 $ \s (a, c) ->
    let (b, s') = f s a
    in  ((b, c), s')

-- | Sequential feedback: c from step n is input c at step n+1.
-- State is (s, c). Initial c is undefined but never forced
-- for well-formed machines.
instance ArrowLoop MealyM where
  loop (MealyM s0 f) = MealyM (s0, initC) step
    where
      initC = error "MealyM.loop: initial feedback demanded before first step"
      step (s, c) a =
        let ((b, c'), s') = f s (a, c)
        in  (b, (s', c'))

instance Profunctor MealyM where
  dimap f g (MealyM s0 step) = MealyM s0 $ \s a ->
    let (b, s') = step s (f a)
    in  (g b, s')

instance Strong MealyM where
  first' = first

-- | One step: produce output and updated machine.
drive :: MealyM a b -> a -> (b, MealyM a b)
drive (MealyM s f) a =
  let (b, s') = f s a
  in  (b, MealyM s' f)

-- | Run a list, return outputs and final machine.
driveList :: MealyM a b -> [a] -> ([b], MealyM a b)
driveList m []     = ([], m)
driveList m (x:xs) =
  let (b,  m')  = drive m x
      (bs, m'') = driveList m' xs
  in  (b:bs, m'')

-- | Run a list, return outputs only.
stepList :: MealyM a b -> [a] -> [b]
stepList m xs = fst (driveList m xs)

-- | Stateless function lift.
stateless :: (a -> b) -> MealyM a b
stateless = arr

-- | Explicit initial state and transition.
withState :: s -> (s -> a -> (b, s)) -> MealyM a b
withState = MealyM

-- | Running accumulation, emit total after each step.
accum :: (b -> a -> b) -> b -> MealyM a b
accum f s0 = MealyM s0 $ \s a ->
  let s' = f s a in (s', s')

-- | Count inputs seen so far.
count :: MealyM a Int
count = MealyM 0 $ \n _ -> (n + 1, n + 1)

-- | Hold a value until a Just arrives, emit current held value.
latch :: a -> MealyM (Maybe a) a
latch a0 = MealyM a0 $ \held new ->
  let held' = maybe held Prelude.id new
  in  (held', held')

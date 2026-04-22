{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | Delimited continuations for Circuit feedback loops.
--
-- Uses GHC 9.6+ primitives (prompt#, control0#) to implement Trace
-- for Kleisli IO with Either tensor, avoiding deep recursion.

module Circuit.GoI
  ( PromptTag,
    newPromptTag,
    prompt,
    control0,
    loopIO,
  )
where

import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
import GHC.IO (IO (..))
import Control.Arrow (Kleisli (..))
import Circuit (Circuit (..), Trace (..))

-- ---------------------------------------------------------------------------
-- Primop wrappers
-- ---------------------------------------------------------------------------

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO \s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #)

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
--
--   The continuation k, when called with a value, returns to the prompt
--   and resumes from there (−F− semantics).
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- ---------------------------------------------------------------------------
-- Trace instance
-- ---------------------------------------------------------------------------

-- | Trace for Kleisli IO with Either tensor using delimited continuations.
--
--   The key: prompt is inside the loop, so every iteration re-establishes
--   the boundary. When control0 fires, it jumps back to the nearest prompt.
instance {-# OVERLAPPING #-} Trace (Kleisli IO) Either where
  trace (Kleisli body) = Kleisli \initial -> do
    tag <- newPromptTag
    let
      loop x = prompt tag $
        body x >>= \case
          Right c -> pure c
          Left a  -> control0 tag \k -> k (loop (Left a))
    loop (Right initial)

  untrace (Kleisli f) = Kleisli \case
    Left a  -> pure (Left a)
    Right b -> Right <$> f b

-- ---------------------------------------------------------------------------
-- Helper
-- ---------------------------------------------------------------------------

-- | Convenient wrapper for simple IO feedback loops.
--
--   @loopIO step@ creates a Circuit that runs @step@ for each iteration,
--   treating both entry and loop states uniformly.
loopIO :: (a -> IO (Either a b)) -> Circuit (Kleisli IO) Either a b
loopIO step = Loop (Kleisli \case
  Right x -> step x
  Left  x -> step x)

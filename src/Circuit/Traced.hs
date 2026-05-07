{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | Trace typeclass, Circuit GADT, and instances for feedback in circuits.
--
-- Supports any base arrow with different tensor types (,) and Either.
-- Includes delimited-continuation implementation for Kleisli IO.

module Circuit.Traced
  ( Trace (..),
    (⥀),
    (↯),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
    whileK,
  )
where

import Control.Arrow (Kleisli (..))
import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
import GHC.IO (IO (..))

-- $setup
-- >>> :set -XNoRequiredTypeArguments
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Control.Category ((>>>))
-- >>> import Circuit.Traced

-- | A traced profunctor over tensor @t@.
--
-- This class packages strength and co-strength operations equivalent to
-- those in the @profunctors@ package, with the tensor parameterised:
--
-- @
--   Trace p (,)     ≅  Strong p + Costrong p
--     where untrace = first'    and  trace = unfirst
--
--   Trace p Either  ≅  Choice p + Cochoice p
--     where untrace = left'     and  trace = unleft
-- @
--
-- Users who want to plug @profunctors@-shaped types into Circuit can
-- write the bridge instance themselves; we don't depend on @profunctors@
-- here to keep the library at @base@ only.
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- | Symbolic alias for 'trace'.
infixr 9 ⥀
(⥀) :: Trace arr t => arr (t a b) (t a c) -> arr b c
(⥀) = trace

-- | Symbolic alias for 'untrace'.
infixr 9 ↯
(↯) :: Trace arr t => arr b c -> arr (t a b) (t a c)
(↯) = untrace

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and output @c@
-- are produced simultaneously.
--
-- === Fibonacci stream
--
-- >>> take 5 $ trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) ()
-- [0,1,1,2,3]
instance {-# OVERLAPPABLE #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- | The cochoice trace iterates: @Left@ feeds back, @Right@ terminates.
--
-- === Counting loop
--
-- >>> trace (\x -> case x of Right n | n < 3 -> Left (n + 1); _ -> Right ()) (0 :: Int)
-- ()
--
-- >>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
-- 3
instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

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

-- | Trace for Kleisli IO with Either tensor using delimited continuations.
--
-- The key: prompt is inside the loop, so every iteration re-establishes
-- the boundary. When control0 fires, it jumps back to the nearest prompt.
--
-- === Counting with IO effects
--
-- >>> :{
-- let stepK :: Either Int () -> IO (Either Int Int)
--     stepK (Right ()) = pure (Left 0)
--     stepK (Left n) | n < 3 = pure (Left (n + 1))
--     stepK (Left n) = pure (Right n)
-- in runKleisli (trace (Kleisli stepK)) ()
-- :}
-- 3
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

-- | While loop in Kleisli IO using the Either trace.
--
-- @whileK step@ runs @step@ repeatedly until it returns @Left r@,
-- threading the state through the feedback channel.
--
-- === Sum [1..n]
--
-- >>> :{
-- let sumStep (n, acc) | n <= 0    = pure (Left acc)
--                      | otherwise = pure (Right (n - 1, acc + n))
-- in whileK sumStep (5, 0)
-- :}
-- 15
whileK :: (s -> IO (Either r s)) -> s -> IO r
whileK step = runKleisli (trace (Kleisli body))
  where
    body (Right s) = swapRL <$> step s
    body (Left s)  = swapRL <$> step s
    swapRL (Right s) = Left s   -- continue -> feedback
    swapRL (Left r)  = Right r  -- done -> output

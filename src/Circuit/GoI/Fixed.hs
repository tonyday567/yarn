{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.GoI.Fixed where

import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
import GHC.IO (IO (..))
import Control.Arrow (Kleisli (..))
import Circuit (Trace (..))

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO \s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #)

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- Fixed Trace instance: prompt is inside the loop, created fresh each time
instance Trace (Kleisli IO) Either where
  trace (Kleisli body) = Kleisli \initial -> do
    tag <- newPromptTag
    let
      loop :: Either a b -> IO b
      loop x = prompt tag $
        body x >>= \case
          Right c -> pure c
          Left a  -> control0 tag \k -> k (loop (Left a))
    loop (Right initial)

  untrace (Kleisli f) = Kleisli \case
    Left a  -> pure (Left a)
    Right b -> Right <$> f b

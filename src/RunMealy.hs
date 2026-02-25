{-# LANGUAGE RankNTypes #-}

-- | Clean interpreter: Traced MealyM -> MealyM
-- Built from scratch without hidden complexity

module RunMealy
  ( runMealy
  ) where

import Data.Function (fix)
import Prelude hiding (id, (.))
import qualified Prelude

import MealyM (MealyM (..), mkMealy, withMealy)
import Traced (Traced (..))

-- | Interpret Traced MealyM as MealyM
-- Mirror the structure of runFn but for MealyM's three-function signature
runMealy :: Traced MealyM a b -> MealyM a b

-- Pure: identity Mealy
-- Takes any input, uses it as state, returns it as output
runMealy Pure = mkMealy Prelude.id (\_ a -> (a, a)) Prelude.id

-- Lift: return the MealyM as-is
runMealy (Lift m) = m

-- Compose: sequence two MealyM machines
-- h processes first, g processes h's output
runMealy (Compose g h) =
  withMealy (runMealy h) $ \hi hs he ->
    withMealy (runMealy g) $ \gi gs ge ->
      mkMealy
        (\a -> 
          let t = hi a              -- h's initial state
              b = he t              -- h's extracted output
              s = gi b              -- g's initial state
          in (s, t))
        (\(s, t) a ->
          let (b, t') = hs t a      -- h's step: returns (output, new_state)
              (out, s') = gs s b    -- g's step: takes h's output
          in (out, (s', t')))
        (\(s, _) -> ge s)           -- g's extract on g's state

-- Loop: feedback - tie output back to input
-- p processes (a, c) and outputs (b, c)
-- We use fix to establish the lazy knot on the output pair
runMealy (Loop p) =
  withMealy (runMealy p) $ \fi fs fe ->
    mkMealy
      (\a -> 
        -- Knot: compute initial state using fix on the output
        -- output :: (b, c) where c feeds back
        let output = fix (\(_, c) -> 
              let (out, _) = fs (fi (a, c)) (a, c)
              in out)
        in fi (a, snd output))
      (\s a ->
        -- Step: extract feedback c from current state, use in next step
        let (_, c) = fe s
            ((b, _), s') = fs s (a, c)
        in (b, s'))
      (\s -> fst (fe s))

module Adapt
  ( adaptiveMultiScale,
    adaptiveMealy,
  )
where

import Control.Category
import Data.Mealy

-- | Two averagers at different base rates
-- The fast one runs at r, the slow one runs at r^4
-- The second scale's r is computed from the ratio of the two means
adaptiveMultiScale :: Double -> Mealy Double (Double, Double)
adaptiveMultiScale baseR =
  (,) <$> fast <*> slow
  where
    fast = ma baseR
    slow = ma (baseR ^ (4 :: Integer))

-- | Now the adaptive version: slow decay rate is driven by fast/slow ratio
-- We need the fast mean to compute r for the slow accumulator
-- This is just Applicative composition - fast state is available to slow
adaptiveMealy :: Double -> Mealy Double (Double, Double)
adaptiveMealy baseR = M inject step extract
  where
    inject x =
      let s_fast = Averager (x, 1)
          s_slow = Averager (x, 1)
       in (s_fast, s_slow)

    step (s_fast, s_slow) x =
      let s_fast' = runStep baseR s_fast x
          r = adaptiveR s_fast'
          s_slow' = runStep r s_slow x
       in (s_fast', s_slow')

    extract (s_fast, s_slow) = (av s_fast, av s_slow)

    runStep r (Averager (s, c)) x = Averager (r * s + x, r * c + 1)

    adaptiveR s =
      let m = abs (av s) + 1e-8
       in min 0.99 (max 0.01 (1.0 / m))

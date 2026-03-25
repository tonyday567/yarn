-- Test: Adaptive multi-scale mealy machine
-- Goal: Verify that the slow track adapts faster after a step change
-- than a fixed-rate moving average would

import Adapt
import Data.Mealy (scan)

testAdaptive :: IO ()
testAdaptive = do
  putStrLn "Testing adaptiveMealy with step change at 500"
  let xs = replicate 500 0.0 <> replicate 500 1.0 -- step change at 500
      result = scan (adaptiveMealy 0.9) xs
      fast = fst <$> result
      slow = snd <$> result
  putStrLn "Step | Fast Track | Slow Track"
  putStrLn "-----+------------+------------"
  -- print every 100 steps
  mapM_ (\(step, f, s) -> printRow step f s) $
    zip3 [0, 100 .. 900] (everyNth 100 fast) (everyNth 100 slow)
  putStrLn ""
  putStrLn "Expected: slow track should accelerate to ~1.0 faster after step 500"
  putStrLn "than a fixed ma(0.9^4) ≈ 0.656 would."
  where
    everyNth n xs = [xs !! i | i <- [0, n .. length xs - 1]]
    printRow step f s =
      putStrLn $
        show step ++ " | " ++ padRight 10 (show f) ++ " | " ++ padRight 10 (show s)
    padRight n s = s ++ replicate (max 0 (n - length s)) ' '

main :: IO ()
main = testAdaptive

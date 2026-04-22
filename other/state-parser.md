# State Parser

State-based parser using `(,)` tensor.

Demonstrates:
- Pure Circuit using the standard `(->)` arrow
- Lazy knot-tying via the `(,)` tensor
- Feedback carries remaining input + accumulator
- Exit happens when condition fails

## Implementation

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Examples.StateParser where

import Circuit
import Prelude hiding (id, (.))

-- | State-based parser using (,) tensor.
--   Feedback carries the remaining input + accumulator.
--   Exit path (Right) signals "parsing finished".

type ParserState a = (String, a)          -- (remaining input, accumulator)

manyDigits :: Circuit (->) (,) String Int
manyDigits = Loop $ \(s, acc) ->
  if not (null s) && head s `elem` ['0'..'9']
    then let d = head s
             rest = tail s
         in (rest, acc * 10 + read [d])     -- continue
    else (s, acc)                           -- exit with current acc

parseNumber :: String -> Int
parseNumber s = snd $ run manyDigits (s, 0)

demoParser :: IO ()
demoParser = do
  print $ parseNumber "12345abc"   -- should print 12345
  print $ parseNumber "no digits"  -- should print 0
```

## Notes

This uses the pure `Circuit (->) (,)` with standard lazy knot-tying. The `(,)` tensor creates the feedback pair; both sides exist simultaneously in the lazy evaluation. No stack risk here because it's pure recursion optimized by lazy evaluation.

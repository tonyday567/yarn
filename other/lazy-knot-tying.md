# Lazy Knot-Tying

lazy knot-tying is a significant architectural feature of GHC, and thus Haskell usage.

For circuits, the canonical knot-tie is unsecond from profunctors.

We choose to make the first element of the tuple the type that gets eliminated by running the function. The usual example is loop from arrows which is akin to unfirst and eliminates the second tuple. We swap so that we can adopt consistent tensor actions to underlying categories upstream: (,) a, Either a and These a.

```haskell
import Data.Function (fix)
import Debug.Trace

-- | Tie the knot: convert a feedback function to a forward function.
--
-- >>> unsecond (\(c, a) -> (a + 10, c + a)) 5
-- 20
unsecond :: ((c, a) -> (c, b)) -> (a -> b)
unsecond f a = b where (c, b) = f (c, a)
```

The output b depends on c, and c itself is computed from the input a. The knot forces a consistent fixed point:

```
biasedAcc 5
  = b
  where (c, b) = f (c, 5)
        f (c_in, x) = (x + 10, c_in + x)
```

Core reduction trace (what actually happens under laziness):

```
b is demanded → evaluate right-hand side of the where.
f (c, 5) is called. The argument tuple is a thunk (c, 5).
f pattern-matches: c_in = c (still a thunk), x = 5.
First component of result: x + 10 = 15 (no dependency on c_in → no black hole).
Second component of result: c_in + x → thunk (c + 5).
The let-binding now gives us the pair (15, c + 5).
Therefore c := 15 and b := 15 + 5 = 20.
```

The back-edge c is only forced after the new value for c has been produced by the first component. Laziness + the simultaneous let binding makes the cycle resolve cleanly.

## Examples

```haskell
-- | a "biased accumulator"
-- Given input a, return (a + 10) + a, but the +10 is stored in the eliminated feedback c.
--
-- >>> biasedAcc 5
-- 20
biasedAcc :: Int -> Int
biasedAcc = unsecond $ \(c, a) -> (a + 10, c + a)
```

You can add a trace if you want to make the unrolling visible at runtime:

```haskell
-- | Show a trace of the lazy-knot tie
--
-- >>> biasedAccTrace 5
-- new c = 15
-- using c = 15
-- 20
biasedAccTrace :: Int -> Int
biasedAccTrace = unsecond $ \(c, a) ->
  (trace ("new c = " ++ show (a + 10)) (a + 10),
   trace ("using c = " ++ show c) (c + a))
```

(The "using c" line appears after "new c" because the thunk for the second component is forced only when b is demanded.)

## Large-structure example

The eliminated type c can be an arbitrarily large lazy structure that refers to itself.

```haskell
-- | Given a list of coin denominations, compute the minimum number of coins
-- needed to make amount 'n'. The feedback 'c' is the entire DP table.
--
-- >>> minCoins [1,2,6,24,1024] 40
-- 5
minCoins :: [Int] -> Int -> Int
minCoins coins = unsecond $ \(table, n) ->
  let minCoins' 0 = 0
      minCoins' k = minimum [1 + table !! (k - c) | c <- coins, c <= k]
  in ( [ minCoins' k | k <- [0..] ]   -- new table = infinite lazy list
     , table !! n )                    -- result = lookup in the tied table
```

What's happening:

- table is an infinite list [0, 1, 2, …] where each entry is defined in terms of earlier entries and itself via the knot.

- The first component of f produces the whole table (lazily).
- The second component just indexes into it.
- Because of laziness the table is built on demand, exactly once, with perfect sharing — exactly the classic "tying the knot" DP trick, but packaged inside unsecond so the recursion is hidden inside the eliminated type.

This is a pure, referentially-transparent dynamic-programming table with no explicit Data.Array or fix/letrec boilerplate. The knot does the heavy lifting.

## Fixed-Point Form

For reference, here's the equivalent to the main implementation using explicit fixed-point:

```haskell
unsecond' :: ((c, a) -> (c, b)) -> (a -> b)
unsecond' f a = snd (fix (\(c, _) -> f (c, a)))
```

This pattern is often seen in refactorings.

## Running the examples

```haskell
main :: IO ()
main = do
  putStrLn "biasedAcc 5:"
  print (biasedAcc 5)
  putStrLn "minCoins [1,2,6,24,1024] 40:"
  print (minCoins [1,2,6,24,1024] 40)
```

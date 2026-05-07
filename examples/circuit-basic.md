⟝ circuit-basic 

# While Loop — Hyper vs Circuit

The simplest recursive pattern: a step function `s -> Either r s`, iterate
until `Left r`, return `r`.  This card shows the same loop in both encodings.

```haskell
-- $setup
-- >>> import Circuit (Hyper (..), Circuit (..), Trace (..), run, lower)
-- >>> import Circuit.Hyper qualified as Hyper
-- >>> import Circuit.Circuit qualified as Circuit
-- >>> import Prelude hiding (id, (.))
```

---

## The Step Function

```haskell
-- | One step: return result (Left) or continue with new state (Right).
type Step s r = s -> Either r s
```

Example: count down from `n`, return the count of steps:

```haskell
countdown :: Step Int Int
countdown n
  | n <= 0    = Left 0       -- done
  | otherwise = Right (n - 1)  -- continue
```

---

## Hyper Version

The recursion lives in `run` — the self-referential knot. The step function
is used directly, with the continuation `k` threaded by `run`.

```haskell
whileH :: Step s r -> s -> r
whileH step = run h
  where
    h :: Hyper (s -> r) (s -> r)
    h = Hyper $ \k s ->
      case step s of
        Left r  -> r
        Right s' -> invoke k h s'
```

Trace: `run h s0 = invoke h (Hyper run) s0`. The first call unwraps `h`,
evaluates `step s0`. If `Left r`, returns `r`. If `Right s1`, calls
`invoke (Hyper run) h s1 = run h s1`. The continuation `k = Hyper run` is
`run` repackaged — the knot closes through the type.

```haskell
-- >>> whileH countdown 5
-- 0
-- >>> whileH countdown 0
-- 0
```

---

## Circuit Version

The recursion lives in `trace` — the `Trace (->) Either` instance iterates
the feedback channel until it produces `Right`. The step function must be
adapted: `Either` in `Loop` uses `Left` as the feedback channel and `Right`
as output. Our `Step` uses `Left` as output and `Right` as continue — so we
swap.

```haskell
whileC :: Step s r -> s -> r
whileC step = lower (Loop (Lift step'))
  where
    step' :: Either s s -> Either s r
    step' = either swapRL swapRL
    -- Both Left (feedback) and Right (fresh input) carry an s.
    -- Apply step, then swap: continue → Left (feedback), done → Right (output).
    swapRL (Left r)  = Right r   -- result  → output channel
    swapRL (Right s) = Left s    -- continue → feedback channel
```

Equivalently, using `trace` directly (without `Circuit` constructors):

```haskell
whileT :: Step s r -> s -> r
whileT step = trace step'
  where step' = either swapRL swapRL
        swapRL (Left r)  = Right r
        swapRL (Right s) = Left s
```

Trace: `trace step' s0` feeds `Right s0` to `step'`. If `step s0 = Left r`,
then `step' (Right s0) = Right r` — trace returns `r`. If `step s0 = Right s1`,
then `step' (Right s0) = Left s1` — trace feeds `Left s1` back to `step'`,
iterating.

```haskell
-- >>> whileC countdown 5
-- 0
-- >>> whileC countdown 0
-- 0
-- >>> whileT countdown 5
-- 0
```

---

## Where the Recursion Lives

```haskell
-- Hyper: run ties the knot
run :: Hyper a a -> a
run h = invoke h (Hyper run)       -- self-reference in the type

-- Circuit: trace iterates the channel
trace :: (Either a b -> Either a c) -> b -> c
trace f b = case f (Right b) of
  Right c -> c                     -- done
  Left a  -> trace f a             -- feedback
```

| Aspect | Hyper | Circuit |
|--------|-------|---------|
| Recursion site | `run` (self-knot) | `trace` (channel iteration) |
| Step shape | `s -> Either r s` (unchanged) | `Either s s -> Either s r` (channel-adapted) |
| Continuation | `k :: Hyper (s→r) (s→r)`, passed explicitly | Implicit in `Either` Left/Right |
| Termination | `Left r` — ignore continuation | `Right c` — trace stops iterating |
| Continue | `Right s'` — call `invoke k h s'` | `Left a` — trace feeds back |

---

## The Convention Swap

Both encodings use `Either` but with opposite conventions:

| Branch | `Step s r` (while loop) | `Trace (->) Either` (Circuit) |
|--------|-------------------------|-------------------------------|
| `Left` | **Result** — done, return `r` | **Feedback** — iterate again |
| `Right` | **Continue** — next state `s` | **Output** — done, return `c` |

This is why `swapRL` is needed to bridge them. The hyperfunction version
avoids Either altogether inside the loop body — the continuation is passed
explicitly as `k`, and the step just returns a value or a new state.

---

## A Larger Example: Sum [1..n]

```haskell
sumStep :: Step (Int, Int) Int     -- (current n, accumulated sum)
sumStep (n, acc)
  | n <= 0    = Left acc
  | otherwise = Right (n - 1, acc + n)

-- >>> whileH sumStep (5, 0)
-- 15
-- >>> whileC sumStep (5, 0)
-- 15
```

---

## The Mendler Case in Action

For `Circuit`, the `Loop` constructor is eliminated by `lower`. The
Mendler case is what makes this work when `Loop` appears on the left
of a `Compose`:

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

For our simple `whileC`, there is no `Compose` — just a bare `Loop`:

```haskell
lower (Loop (Lift step'))
  = trace step'                    -- base case, no Mendler needed
```

The Mendler case comes into play when you compose loops:

```haskell
-- Two loops in sequence: run whileC step1, feed result to whileC step2
pipeline :: Circuit (->) Either s s
pipeline = Loop (Lift step2') `Compose` Loop (Lift step1')

lower pipeline
  = trace (step2' . untrace (lower (Loop (Lift step1'))))   -- Mendler
  = trace (step2' . untrace (trace step1'))
```

This is where `Circuit` earns its keep — composing feedback structures.
For a single while loop, `trace` directly is simplest.

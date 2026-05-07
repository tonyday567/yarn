⟝ harpie 

# HarpieHyper — Memoizing Hyperfunctions via Representable Array

This card shows how to apply the Rep.hs memoization pattern (see
[yaya.md](yaya.md#rephs-memoization-via-lambek)) to harpie's `Array s`,
a fixed-shape multidimensional array backed by `Data.Vector`.

---

## Why harpie?

harpie's `Harpie.Fixed.Array (s :: [Nat]) a` is `Representable`:

```haskell
instance KnownNats s => Representable (Array s) where
  type Rep (Array s) = Fins s
  tabulate :: (Fins s -> a) -> Array s a
  index    :: Array s a -> Fins s -> a
```

`Fins s` is a finite index type for a shape `s`. For shape `[2,3,4]`,
there are 24 indices. `tabulate` eagerly allocates a `Vector` of 24 entries;
`index` does an O(1) lookup.

This is exactly the representable functor that Rep.hs needs: a finite,
materialized table with constant-time lookup.

---

## The Bridge Type

Kmett's Rep.hs GADT, instantiated at `g = Array s`:

```haskell
-- Rep.hs:
--   data Hyper a b where
--     Hyper :: Representable g => g (g a -> b) -> Rep g -> Hyper a b

-- With g = Array s, Rep g = Fins s:
Hyper :: Array s (Array s a -> b) -> Fins s -> Hyper a b
```

Unpacked as a product type:

```haskell
data HarpieHyper s a b = HH
  { table :: Array s (Array s a -> b)  -- ^ memo table: at each position,
                                       --   a function from continuation-array to result
  , pos   :: Fins s                    -- ^ current position
  }
```

The `Array s (Array s a -> b)` is the memoization cache. Each entry at
position `i :: Fins s` is a function `Array s a -> b` that, given the
full continuation array, produces the result at position `i`. The `Fins s`
selects which entry to use.

---

## Tabulation: Building the Table

The table is built by tabulating across all positions:

```haskell
tabulateHyper
  :: forall s a b. KnownNats s
  => (Fins s -> (Fins s -> a) -> b)  -- pointwise spec
  -> HarpieHyper s a b
tabulateHyper f = HH table startPos
  where
    startPos = fins (replicate (rankOf @s) 0)

    table :: Array s (Array s a -> b)
    table = tabulate $ \i arrA ->
      f i (\j -> index arrA j)
    -- At each position i, given the continuation-array arrA,
    -- call f i with the continuation viewed as Fins s -> a.
```

This eagerly allocates a `Vector` of `sizeOf @s` entries. Each entry
closes over the position `i` and the user-supplied function `f`.

---

## invoke: The Self-Referential Knot

The critical operation. Given a hyper `h :: HarpieHyper s a b` and its
dual continuation `k :: HarpieHyper s b a`, produce `b`:

```haskell
invoke
  :: forall s a b. KnownNats s
  => HarpieHyper s a b -> HarpieHyper s b a -> b
invoke (HH tab_h pos_h) (HH tab_k pos_k) =
  index tab_h pos_h contArray
  where
    -- contArray :: Array s a
    -- Built from the dual table tab_k, referencing itself through tab_h.
    -- This is the self-referential knot, resolved via tabulate/index.
    contArray = tabulate $ \j ->
      let psi_j = index tab_k j        -- :: Array s b -> a
          -- To feed psi_j, we need Array s b. We build it from tab_h
          -- applied to... contArray itself.
          arrB = tabulate $ \i ->
            let phi_i = index tab_h i  -- :: Array s a -> b
            in phi_i contArray
      in psi_j arrB
```

For a finite shape `s` with `n = sizeOf @s` positions, this is a system
of `n` equations. `tabulate` allocates the vectors; lazy evaluation resolves
the knot pointwise.

**The memoization payoff:** each `phi_i` at position `i` is pre-computed
during tabulation. `invoke` does O(1) table lookups at each step, rather
than recursively unfolding a closure chain.

---

## Example: Fibonacci via Memo Table

```haskell
-- Shape: 1D array of length n
fibHyper :: forall n. KnownNat n => HarpieHyper '[n] Int Int
fibHyper = tabulateHyper @'[n] $ \(UnsafeFins [i]) kont ->
  if i == 0 then 0
  else if i == 1 then 1
  else kont [i - 1] + kont [i - 2]
```

The table `Array '[n] (Array '[n] Int -> Int)` pre-allocates `n` entries.
At position `i`, the entry is a function that, given the continuation array
(containing fib(0)..fib(n-1)), computes `kont[i-1] + kont[i-2]`.

**Without memoization** (plain `Hyper a a`): each call unfolds the recursive
chain. Fibonacci takes O(2^n) time.

**With memoization** (HarpieHyper): each position is looked up in the
pre-built table. `invoke` traverses the table once, O(n) time, O(n) space.

---

## cata: Memoizing Catamorphism

Rep.hs provides `cata'`, a catamorphism that threads a memo table through
the fold. For `Array s`:

```haskell
cataHarpie
  :: forall s a b r. KnownNats s
  => ((Array s a -> b) -> r)  -- ^ extract result from continuation
  -> HarpieHyper s a b        -- ^ the hyperfunction
  -> r
cataHarpie extract (HH tab pos) =
  extract (\arrA -> index tab pos arrA)
```

Simpler than the general Rep.hs `cata'` because `Array s` is already
fully tabulated. The fold just indexes into the pre-built table.

---

## run: Tying the Diagonal

When `a = b`, the hyperfunction can self-apply:

```haskell
runHyper :: forall s a. KnownNats s => HarpieHyper s a a -> a
runHyper h = invoke h h
```

This ties the full knot: the table at position `pos_h` is applied to
a continuation array built from the same table. For finite `s`, this
produces a result in O(|s|) time.

---

## Why This Matters

The plain `Hyper a b` newtype is a coinductive structure — every observation
unfolds another layer. It's elegant but offers no control over evaluation
strategy.

The Rep.hs pattern — and harpie's `Array s` as the representable functor —
makes the state space **explicit and finite**. Instead of an infinite
coinductive chain, you get:

1. A pre-allocated `Vector` of size `n`
2. O(1) table lookups at each step
3. A finite system of equations resolved via lazy evaluation
4. Automatic memoization: each position is computed at most once

The tradeoff: the shape `s` must be known at compile time (type-level
`[Nat]`). For dynamic shapes, use `Harpie.Array` (value-level shape) with
a different representable strategy (e.g., `Map Int` as the functor).

---

## Connection to the Narrative

The yaya bridge ([yaya.md](yaya.md)) proved `Hyper a b ≅ Fix ((· → a) → b)`.
The Rep.hs pattern generalises this to `Hyper a b ≅ Fix (Ran (Const a) (Const b))`
with a representable functor mediating the fixpoint. Harpie's `Array s`
is one concrete choice of representable functor — the one that gives
dense, vector-backed memoization.

```haskell
-- The full correspondence:
Hyper a b  ≅  Fix (Ran (Const a) (Const b))
           ≅  Fix (HyperF a b)              -- yaya bridge
           ≅  HarpieHyper s a b             -- with g = Array s, Rep g = Fins s
```

The final step is choosing `g`. `Array s` gives O(1) indexing and O(n)
space for shape `s`. Other choices (`Map k`, `IntMap`, `HashMap`) give
different time/space tradeoffs — all fitting the same Rep.hs interface.

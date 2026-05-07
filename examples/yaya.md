⟝ yaya 

# Hyper ≅ Fix (Ran (Const a) (Const b)) — The yaya Bridge

For background on both libraries see [hyper-basic.md](hyper-basic.md) (Circuit.Hyper)
and the [yaya repo](https://github.com/sellout/yaya) (recursion schemes over pattern
functors). This card proves the isomorphism conjectured in the narrative
([04-hyper.md](../other/04-hyper.md)):

> **`Hyper a b  ≅  Fix (Ran (Const a) (Const b))`**

and shows how yaya-style recursion schemes apply directly to `Hyper a b`.

---

## The Surprise

`Hyper a b` is the fixpoint of `(x → a) → b`. The parameter `x` appears in
double-contravariant position:

```
(x → a) → b
 ─┬──    ─┬─
  │       └─ contravariant (outer →)
  └─ contravariant (inner →)
```

**Contravariant of contravariant = covariant.** So `(x → a) → b` has a
perfectly valid `Functor` instance:

```haskell
fmap :: (x → y) → ((x → a) → b) → ((y → a) → b)
fmap f h = \g → h (g . f)
```

GHC derives this. The fixpoint is standard. The whole yaya zoo applies.

---

## The Pattern Functor

```haskell
{-# LANGUAGE DeriveFunctor #-}

-- | The base functor whose fixpoint is Hyper.
--
-- @HyperF a b x = (x → a) → b@.
newtype HyperF a b x = HyperF { runHyperF :: (x → a) → b }
  deriving Functor
```

The right Kan extension `Ran (Const a) (Const b)` is exactly this endofunctor:

```
Ran (Const a) (Const b) x  ≅  ∀c. (x → Const a c) → Const b c
                           ≅  ∀c. (x → a) → b
                           ≅  (x → a) → b
```

The `∀c` disappears because `Const b c = b` for all `c`. The fixpoint
equation `X ≅ (X → a) → b` is what matters, and `HyperF a b` captures it
precisely.

---

## Standard Fix

```haskell
-- | Standard Fix (identical to yaya's `Yaya.Fold.Native.Fix`).
newtype Fix f = Fix { unFix :: f (Fix f) }
```

`Fix (HyperF a b)` is the yaya-compatible encoding of `Hyper a b`. Unfolding:

```
Fix (HyperF a b)
  ≅ HyperF a b (Fix (HyperF a b))
  ≅ (Fix (HyperF a b) → a) → b
```

Meanwhile `Hyper a b` unfolds:

```
Hyper a b
  ≅ Hyper b a → b                                (unwrap newtype)
  ≅ (Hyper a b → a) → b                          (unwrap inner newtype)
  ≅ (Self → a) → b
```

Same fixpoint equation. The two types satisfy the same recursive equation.
By Lambek's lemma they are isomorphic as final coalgebras.

---

## The Isomorphism

```haskell
toFix :: Hyper a b -> Fix (HyperF a b)
toFix h = Fix (HyperF $ \k -> invoke h (Hyper $ \h' -> k (toFix h')))

fromFix :: Fix (HyperF a b) -> Hyper a b
fromFix (Fix (HyperF f)) = Hyper $ \k -> f (\hfix -> invoke k (fromFix hfix))
```

**`toFix`** is self-contained. The inner `Hyper $ \h' -> k (toFix h')`
threads the continuation through the recursive unfolding. The type of the
inner expression is `Hyper b a`, which is exactly what `invoke h` expects.

**`fromFix`** is a plain fold. For each layer, it wraps the continuation
`k :: Hyper b a` through the recursive call.

---

### Point-Free: The Algebra and Coalgebra

At the one-step level — before `Fix` ties the recursive knot — `toFix` and
`fromFix` decompose into a coalgebra and an algebra on `HyperF`:

```haskell
-- | Coalgebra: peel one layer of Hyper into HyperF.
--
-- > coalg h  =  HyperF . invoke h . Hyper
coalgebra :: Hyper a b -> HyperF a b (Hyper a b)
coalgebra h = HyperF $ invoke h . Hyper
-- invoke h :: Hyper b a -> b
-- Hyper    :: (Hyper a b -> a) -> Hyper b a     (constructor at swapped params)
-- invoke h . Hyper :: (Hyper a b -> a) -> b     = HyperF a b (Hyper a b) ✓

-- | Algebra: wrap one layer of HyperF back into Hyper.
--
-- > alg (HyperF f)  =  Hyper . f . invoke
algebra :: HyperF a b (Hyper a b) -> Hyper a b
algebra (HyperF f) = Hyper $ f . invoke
-- f         :: (Hyper a b -> a) -> b
-- invoke    :: Hyper b a -> Hyper a b -> a       (swapped params)
-- f . invoke :: Hyper b a -> b                   = Hyper a b ✓
```

And the isomorphism factors through them:

```
toFix   = anaFix coalgebra     -- unfold the fixpoint
fromFix = cataFix algebra      -- fold the fixpoint
```

Both are one step. The coalgebra unwraps `Hyper` by calling `invoke h`;
the algebra wraps `Hyper` by calling `invoke k`. The symmetry centers
entirely on `invoke` swapping roles — destructor in `coalgebra`, pre-composed
in `algebra`.

---

### Lambek's Lemma

**Lambek's lemma** (1968): for any initial algebra `α :: F (μF) → μF`,
`α` is an isomorphism with inverse `α⁻¹ = cata (F α)`. Dually for final
coalgebras. In fixpoint terms: the constructor and destructor of a fixpoint
are mutual inverses at the one-step level.

For our bridge:

```
algebra . coalgebra  =  id     -- wrapping after peeling = identity
coalgebra . algebra  =  id     -- peeling after wrapping = identity
```

Proof (the second, the non-trivial direction):

```
coalgebra (algebra (HyperF f))
  = coalgebra (Hyper (f . invoke))
  = HyperF (invoke (Hyper (f . invoke)) . Hyper)
  = HyperF ((f . invoke) . Hyper)
  = HyperF (f . (invoke . Hyper))
  = HyperF (f . id)              -- invoke . Hyper = id (newtype)
  = HyperF f
```

The algebra and coalgebra are mutual inverses *at the `HyperF` level*. The
fixpoint `Fix` just makes the self-reference explicit; the real content is
that `Hyper` is already its own one-step unfold/fold — a direct consequence
of `newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }`.

Lambek's lemma connects to the names in Kmett's library: `roll` and `unroll`
are the algebra and coalgebra respectively. `roll :: HyperF a b (Hyper a b) → Hyper a b`
is the wrap; `unroll :: Hyper a b → HyperF a b (Hyper a b)` is the peel.

---

### Rep.hs: Memoization via Lambek

Kmett's `Control.Monad.Hyper.Rep` generalises this by replacing the
implicit `Hyper` recursion with an explicit representable functor `g`:

```haskell
data Hyper a b where
  Hyper :: Representable g => g (g a -> b) -> Rep g -> Hyper a b
```

A representable functor `g` is isomorphic to `Rep g → _` — it's a
keyed lookup table. The `Hyper` GADT stores a table `g (g a → b)` and
a current key `Rep g`. Each entry in the table maps continuation state
to output.

The `roll`/`unroll` (algebra/coalgebra) in this setting become:

```haskell
unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll (Hyper f x) k = index f x (tabulate (k . Hyper f))
-- Tabulate builds a table from the continuation; index picks entry x.

roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = Hyper (mapH unroll)
-- Builds the table by composing unroll into each entry.
```

These are the *same* algebra and coalgebra as our point-free forms, but
with `g` and `Rep g` threading explicit state space. When `g = Identity`
(`Rep g = ()`), this collapses to the simple newtype — `roll = Hyper`,
`unroll = invoke`.

**The point of Rep.hs**: choose `g = Array` or `g = Map k` to get
*memoization*. Each `Rep g` key stores a function `g a → b`, so repeated
calls to `invoke` at the same state reuse cached results. The `cata` in
Rep.hs is a memoizing catamorphism — it threads a memo table through the
fold, avoiding recomputation of previously-visited states.

In the newtype `Hyper`, `invoke` just calls the stored function — there's
no table, no memoization, just the raw self-reference. Rep.hs makes the
state space inspectable (and cacheable) by splitting the self-reference
into `g` (table) and `Rep g` (key). Lambek's lemma still holds: `roll` and
`unroll` are mutual inverses, just with a representable functor mediating
the knot.

---

## yaya cata via the Bridge

```haskell
type Algebra f a = f a -> a

cataFix :: Functor f => Algebra f a -> Fix f -> a
cataFix alg = alg . fmap (cataFix alg) . unFix

-- | Fold a 'Hyper' using a yaya-style algebra.
hyperCata :: Algebra (HyperF a b) r -> Hyper a b -> r
hyperCata alg = cataFix alg . toFix
```

Any `Algebra (HyperF a b) r` folds a `Hyper a b` into `r`. The algebra
receives `(r → a) → b` and must produce `r`. This constrains `r` to capture
`b` structurally — typically `r = a → b` or `r` includes `b` in a product.

---

## The Observe Algebra — Recovers `lower`

```haskell
-- | Algebra: observe a Hyper as a plain function a → b.
observeAlgebra :: HyperF a b (a -> b) -> (a -> b)
observeAlgebra (HyperF f) a = f (const a)
```

This is the canonical algebra. Given `f :: ((a → b) → a) → b` and an input
`a`, it feeds `const a` (ignore the recursive result, return the input) to `f`,
obtaining `b`.  The identity:

```
hyperCata observeAlgebra  =  lower
```

Proof sketch: by induction on the fixpoint structure. At each layer,
`observeAlgebra` supplies `const a` as the continuation, which is exactly
what `lower h a = invoke h (base a) = invoke h (Hyper (const a))` does. The
`cataFix` recursion threads this through all layers.

```
hyperCata observeAlgebra (base 42) 0  =  lower (base 42) 0  =  42
hyperCata observeAlgebra (lift (+1)) 5  =  lower (lift (+1)) 5  =  6
```

---

## yaya ana via the Bridge

```haskell
type Coalgebra f s = s -> f s

anaFix :: Functor f => Coalgebra f s -> s -> Fix f
anaFix coalg = Fix . fmap (anaFix coalg) . coalg

-- | Unfold a seed into a 'Hyper' using a yaya-style coalgebra.
hyperAna :: Coalgebra (HyperF a b) s -> s -> Hyper a b
hyperAna coalg = fromFix . anaFix coalg
```

A `Coalgebra (HyperF a b) s` is `s → (s → a) → b` — exactly the signature
of Kmett's `ana`. The coalgebra receives a seed `s` and a continuation accessor
`(s → a)`, and must produce `b`. This is the universal anamorphism for
hyperfunctions.

`hyperAna` = Kmett's `ana` (the one now exported from `Circuit.Hyper`).
The bridge shows these are the same function.

---

## Connection to the Narrative

The narrative ([04-hyper.md](../other/04-hyper.md)) characterises `Hyper` as
the Kan-extension fixpoint.  This card provides the constructive proof:

```
Hyper a b  ≅  Fix (Ran (Const a) (Const b))
           ≅  Fix (HyperF a b)
```

- **Before Fix:** `Circuit a b ~ Ran (Const a) (Const b)` (the free category)
- **After Fix:** `Hyper a b = Fix (Ran (Const a) (Const b))` (the traced category)

The Mendler case in `lower` on `Circuit` makes the catamorphism valid.
`toHyper` maps `Circuit → Hyper` as the unique traced functor from the initial
to the final encoding. The bridge in this card shows the converse:
`Hyper` **is** the fixpoint of the Ran functor, and standard recursion
schemes work directly on it through `toFix`/`fromFix`.

---

## The Full yaya Zoo

With the bridge in place, every yaya recursion scheme applies to `Hyper a b`:

| Scheme | Signature | Role |
|--------|-----------|------|
| `cata` | `Algebra f r → Fix f → r` | Fold (inductive) |
| `ana` | `Coalgebra f s → s → Fix f` | Unfold (coinductive) |
| `para` | `GAlgebra (Pair (Fix f)) f r → Fix f → r` | Fold with access to original |
| `apo` | `GCoalgebra (Either (Fix f)) f s → s → Fix f` | Unfold with early return |
| `histo` | `GAlgebra Cofree f r → Fix f → r` | Fold with history |
| `futu` | `GCoalgebra Free f s → s → Fix f` | Unfold with future steps |
| `zygo` | `Algebra f a → GAlgebra (Pair a) f r → Fix f → r` | Fold with helper algebra |
| `mutu` | `GAlgebra (Pair a) f b → GAlgebra (Pair b) f a → Fix f → a` | Mutual recursion |

All accessed via `hyperCata`, `hyperAna`, or their generalised forms composed
with `toFix`/`fromFix`.

---

## Summary

1. `(x → a) → b` is covariant in `x` — double contravariance cancels
2. `Fix (HyperF a b)` is the yaya-compatible encoding of `Hyper a b`
3. `toFix`/`fromFix` are the concrete isomorphism
4. `hyperCata observeAlgebra = lower` — the observe algebra recovers elimination
5. `hyperAna` = Kmett's `ana` — the universal anamorphism
6. The full yaya zoo (cata, ana, para, apo, histo, futu, zygo, mutu) applies

This card is a candidate for `Circuit.Hyper.Fix` once recursion-schemes
integration is addressed. For now it lives here as an example card — a
self-contained proof that the Kan extension narrative is constructively
realised.

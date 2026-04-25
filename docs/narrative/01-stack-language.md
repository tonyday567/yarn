# The Little Stack Language

**Status:** Draft  
**Next:** [02-gadt.md](02-gadt.md)

---

The circuits library grows from five marks — five operations over an abstract type. They form a tiny stack-based language. Everything else in the library is a consequence of making these five operations precise.

```
η   lift      embed a plain arrow
ε   lower     observe / eliminate
⊙   compose   sequential composition
⊲   push      prepend a plain function
⥁   run       tie the knot
```

See [symbols.md](../other/symbols.md) for the full symbol dictionary.

---

## The Five Marks as a Language

```haskell
(⊙)  :: H b c -> H a b -> H a c   -- compose
η    :: (a -> b) -> H a b          -- lift
ε    :: H a b -> (a -> b)          -- lower
(⊲)  :: (a -> b) -> H a b -> H a b -- push
⥁    :: H a a -> a                 -- run
```

These are the semantics of Section 7 in Launchbury, Krstic & Sauerwein (2013), restated in modern notation.

---

## The Six Axioms

These five operations satisfy six axioms. The first three build a free category. The last three add the feedback structure.

```
axiom 1  (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)           associativity
axiom 2  f ⊙ η id     =  f  =  η id ⊙ f          identity
axiom 3  η (f . g)    =  η f ⊙ η g                lift is a functor
axiom 4  ⥁ (η f)      =  fix f                    run is fixed-point
axiom 5  (f ⊲ p) ⊙ (g ⊲ q)  =  (f . g) ⊲ (p ⊙ q) push composition
axiom 6  ⥁ ((f ⊲ p) ⊙ q)    =  f (⥁ (q ⊙ p))    feedback / sliding
```

---

## Push and Run are Compound

Two of the five marks are not primitive — they decompose into simpler terms:

**Push decomposes into lift and compose:**

```haskell
f ⊲ p  =  η f ⊙ p
```

**Run decomposes into lower and fix:**

```haskell
⥁  =  fix . ε
```

Substituting these into axioms 4, 5, 6 reduces the axiom set to three structural roles:

| Axioms | Role | Constructors |
|--------|------|--------------|
| 1, 2, 3 | Free category | `Lift`, `Compose` |
| 4 | Faithful embedding: `ε . η = id` | Interpretation only |
| 5 | Centrality: lifted arrows slide past anything | Free from tensor symmetry |
| 6 | Feedback / sliding | `Loop` constructor |

Axioms 4 and 5 introduce no new constructors. Only axiom 6 does.

---

## The Fibonacci Stream

The language is already powerful enough to express the classic Fibonacci stream:

```haskell
fibs :: Circuit (->) (,) Int Int
fibs = Loop (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
```

The feedback channel `(,)` carries the stream alongside the index. The loop ties the knot: the output stream feeds back into itself to compute successive elements.

Running it:

```haskell
>>> reify fibs 0
0
>>> reify fibs 4
3
```

This example looks simple. It hides a subtlety: a naive interpreter gets the wrong answer on the second iteration. The fix requires exactly one extra pattern match — the Mendler case — which is the operational form of axiom 6. See [02-gadt.md](02-gadt.md).

---

## The Conceptual Stack

The five marks sit at the top of a conceptual tower. Each layer below adds one concept:

```
η ε ⊙ ⊲ ⥁            ← the five marks (this section)
     ↓
Axioms 1–6             ← what the marks must satisfy
     ↓
GADT + Mendler case    ← the unique construction that satisfies them
     ↓
Circuit (initial)      ← the free traced monoidal category
     ⟺
Hyper (final)          ← the coinductive / Church encoding
     ↓
Tensor choice          ← (,) vs Either: dataflow vs coroutines
     ↓
Production use         ← agents, pipes, parsers, backprop
```

Each level adds exactly one concept. The five marks at the top already imply everything below.

---

## This Little Language Scales

Axiom 6 — the feedback axiom — is exactly the sliding axiom of a traced monoidal category. The five marks, taken together, are the generators of the free traced monoidal category over a base arrow. Every operation in the circuits library is a consequence of making these generators precise.

The slogan:

> **Two adjunctions plus one strength.**

- `η ⊣ ε` (lift and lower) — the free/forgetful adjunction — gives you the category structure.
- `Circuit ↔ Hyper` — the initial/final Galois connection — gives you the two encodings.
- Axiom 6 — the sliding axiom — is the one piece of genuine traced-category content.

**Next:** [02-gadt.md](02-gadt.md) — how the axioms force a three-constructor GADT.

---

## References

- Launchbury, Krstic & Sauerwein, "Hyperfunctions" (2013) — original axiom system
- Kidney & Wu, "Hyperfunctions and the monad of streams" (2026) — modern notation
- Joyal, Street & Verity, "Traced monoidal categories" (1996) — categorical foundations
- [symbols.md](../other/symbols.md) — symbol dictionary (single source of truth)

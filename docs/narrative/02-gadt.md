# From Stack Marks to the GADT

**Status:** Draft  
**Prev:** [01-stack-language.md](01-stack-language.md) | **Next:** [03-circuit.md](03-circuit.md)

---

The six axioms from [Section 1](01-stack-language.md) determine the GADT exactly. Three constructors, no more. This section shows why — and why a naive attempt fails.

---

## The GADT Falls Out of the Axioms

Axioms 1–3 (associativity, identity, functoriality of lift) require a free category. That is just two constructors:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
```

Axiom 4 (`ε . η = id`) is a constraint on interpretation — it introduces no new constructor.

Axiom 5 (centrality — lifted arrows slide past anything) holds automatically when the tensor `t` is symmetric. No new constructor.

**Axiom 6 alone forces the third constructor.**

Substituting `f ⊲ p = η f ⊙ p` and `⥁ = fix . ε` into axiom 6:

```
ε ((η f ⊙ p) ⊙ q) = f . ε (q ⊙ p)
```

The right-hand side swaps `p` and `q`. This is not reassociation — it is a genuine swap. A free category built from `Lift` and `Compose` alone cannot produce a swap; composition is directional. To model this swap, a new constructor is needed that carries an explicit feedback channel — one that can be slid across composition.

That constructor is `Loop`:

```haskell
Loop :: arr (t a b) (t a c) -> Circuit arr t b c
```

`Loop` wraps an arrow over a tensor `t`, making the channel type explicit. The tensor `t` is what allows the swap. The `Trace` typeclass provides the operations on `t`:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

---

## The Naive Run

A first attempt at interpretation follows the GADT structure directly:

```haskell
lower (Lift f)      = f
lower (Compose f g) = lower f . lower g
lower (Loop k)      = trace k
```

This compiles. The Fibonacci example runs correctly. It is easy to believe this is complete.

It is not. Substituting `f ⊲ p = Lift f ⊙ p` into axiom 6, the LHS reduces to:

```
lower (Compose (Lift f) (Compose p q)) = f . lower p . lower q
```

The RHS:

```
f . lower (Compose q p) = f . lower q . lower p
```

These are equal only if `lower p` and `lower q` commute. In general they do not.

The naive run fails axiom 6. The Fibonacci example did not catch this because it has no `Compose` wrapping a `Loop` on the left. That structure only surfaces when something is composed *after* a feedback loop.

---

## The Fault Line: Loop on the Left

When a `Loop` appears on the left of a `Compose`, the naive run applies `trace k` immediately and then composes. But axiom 6 requires the right-hand morphism to participate *inside* the trace — to be threaded through `untrace` before `trace` closes the loop.

The naive run gives:

```
lower (Compose (Loop f) g) = trace f . lower g    -- WRONG
```

Axiom 6 requires:

```
lower (Compose (Loop f) g) = trace (f . untrace (lower g))    -- CORRECT
```

The difference: in the correct version, `lower g` is threaded into the feedback channel via `untrace` on every pass. In the naive version it is applied once at entry.

For `(,)`, `untrace = second`. The two versions give the same answer when the loop terminates in one step; they diverge when it iterates. For `Either`, `untrace = fmap` on `Right`, and the two versions produce different results even on the first iteration.

---

## The Mendler Case

The fix is one extra pattern match, inserted before the general `Compose` case:

```haskell
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f)             = f
lower (Compose (Loop f) g) = trace (f . untrace (lower g))   -- Mendler case
lower (Compose f g)        = lower f . lower g
lower (Loop k)             = trace k
```

The order is load-bearing. Without the `Compose (Loop f) g` case appearing before the general `Compose` case, the pattern falls through and produces the naive — incorrect — behaviour.

This is the **Mendler algebra step**: inspecting one syntactic layer before recursing. The Mendler case converts a structural observation into an operational guarantee: when a `Loop` appears at the head of a composition, the trailing morphism is wired into the feedback channel before the trace closes.

Without this case, `Loop` becomes observationally equivalent to `Lift (trace k)` — the feedback channel closes immediately, the loop structure is lost, and `Circuit` collapses to the free category with a fixed-point operator. This is the **degenerate model** that the 2013 paper warns about.

---

## Why Three Constructors and No More

The three constructors cover exactly the three structural roles:

| Constructor | Axioms | Role |
|-------------|--------|------|
| `Lift` | 2, 3 | Embed base arrows; free category unit |
| `Compose` | 1 | Sequential composition |
| `Loop` | 6 | Feedback channel; traced structure |

Adding a `Push` constructor (`Compose . Lift`) would be redundant — it is already a compound term. Adding a `Curry` constructor would give a closed monoidal category, which is strictly more than traced. The GADT is minimal for traced monoidal categories.

The Trace typeclass is separate from the GADT because the choice of tensor `t` is not fixed by the axioms — it is a parameter. The GADT is generic over `t`; the Trace instances for `(,)` and `Either` are concrete choices. See [05-tensor.md](05-tensor.md).

---

## The Historical Path

The abstraction came last. The actual path was:

1. Axiom 6 has a hidden channel implicit in how `⥁` ties the knot.
2. Costrength suggested naming the channel as an explicit tensor `t`.
3. `Loop :: arr (t a b) (t a c) -> Circuit arr t b c` was a guess.
4. The Mendler case was added to make the types line up.
5. What fell out was recognised as a free traced monoidal category.

"Free traced monoidal category", the sliding axiom, and the `Trace` typeclass are the retrospective description of what the construction turned out to be — not the design principle.

---

## Summary

The GADT is forced:

- Axioms 1–3 give `Lift` and `Compose`.
- Axiom 6 (feedback) gives `Loop` and the Mendler case.
- Nothing else is needed.

The Mendler case is the operational content. Everything else — the categorical language, the typeclass, the tensor abstraction — is the retrospective framework that explains why the Mendler case is correct.

**Next:** [03-circuit.md](03-circuit.md) — Circuit as the free traced monoidal category; the universal property; why the degenerate model is ruled out.

---

## References

- Launchbury, Krstic & Sauerwein (2013) — axioms and the degenerate model
- Hasegawa (1997) — sliding as naturality; [hasegawa.md](../other/hasegawa.md)
- [axioms-hyp.md](../other/axioms-hyp.md) — modern axiom presentation
- [axioms-traced.md](../other/axioms-traced.md) — detailed proofs with (,) and Either

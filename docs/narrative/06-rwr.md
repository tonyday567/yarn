# Reflection Without Remorse for Traced Categories

**Status:** Draft  
**Prev:** [05-tensor.md](05-tensor.md) | **Next:** [07-future.md](07-future.md)

---

Van der Ploeg & Kiselyov (2014) solve the left-nested composition problem for monads. The same problem appears in traced categories, and the same solution applies — with the Mendler case playing the role of `viewl`.

---

## The Problem: Left-Nested Composition

In any free structure built from sequential composition, left-nesting is a performance trap:

```
((a . b) . c) . d . e . ...
```

Each `(.)` must traverse the left spine to find the base case. For a list this is O(n²). For a free monad it is the same. For `Circuit` it is the same — and worse: `Loop` gets buried under the left-nesting and collapses to the degenerate model if the Mendler case isn't in place.

Van der Ploeg & Kiselyov establish a hierarchy for solving this:

| Structure | Naive | Efficient (Ran / Fix.Ran) | Inspection mechanism |
|-----------|-------|---------------------------|----------------------|
| Monoid | list | difference list | head/tail |
| Monad | free monad | codensity monad | `viewl` on TCQueue |
| Category | `Cat` | `Queue` (Ran) | `viewl` on type-aligned queue |
| **Traced category** | **`Circuit`** | **`Hyper`** | **Mendler case in `lower`** |

The paper stops at categories. The natural next row is traced categories.

---

## `viewl` is the Mendler Case

The paper's solution requires `viewl` on the type-aligned queue — inspecting the head of the sequence before recursing. Without `viewl`, the interpreter falls through to a general case that buries the structure and produces O(n²) behaviour.

In `lower`, the Mendler case does exactly this:

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

When a `Loop` appears at the head of a composition, **inspect it before recursing into `g`**. Without this case, `lower` falls through to the general `Compose` rule, buries the `Loop`, and produces the degenerate model.

The analogy:

```
Cat  +  viewl      =  Queue              -- RwR for categories
Circuit  +  Mendler  =  Hyper             -- RwR for traced categories
```

---

## The Hidden Sequence

The paper's title refers to the implicit sequence of monadic binds, made explicit by a type-aligned queue. In `Circuit`, the hidden structure is the **feedback channel inside `Loop`**. Both are made explicit by their respective constructions:

- The **type-aligned queue** in RwR makes the bind sequence inspectable
- The **`Loop` constructor** in `Circuit` makes the feedback channel inspectable

Both solve the same problem: making implicit structure explicit so the interpreter can inspect it without traversing the entire left spine first.

---

## `PMonad` and `Trace`

The paper introduces `PMonad` — an alternative to `Monad` where bind takes an explicit type-aligned sequence as its right argument rather than a single continuation:

```haskell
class PMonad m where
  return' :: a -> m a
  (>>^=)  :: m a -> MCExp m a b -> m b
```

This is structurally the same move as the `Trace` class: instead of hiding the feedback channel inside the monad, make it an explicit typed argument:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- observe the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into the channel
```

| RwR concept | Circuits equivalent |
|-------------|---------------------|
| `PMonad` | `Trace` typeclass |
| Type-aligned queue | Explicit tensor `t` in `Loop` |
| `viewl` (head inspection) | Mendler case in `lower` |
| `tsingleton` (single element) | `untrace` (inject one morphism) |
| `val` (observe head) | `trace` (eliminate the channel) |
| Degenerate model (O(n²)) | `lower` without Mendler (collapses to `Lift (trace k)`) |

---

## Performance: Circuit vs Hyper

The RwR analogy also explains the performance story:

**`Circuit` (naive):** Left-nested `Compose` produces O(n²) traversal. Worse: if `Loop` gets buried under left-nesting without the Mendler case, the traced structure collapses.

**`Circuit` (with Mendler):** The Mendler case prevents collapse, but left-nested `Compose` still requires O(n) traversal to find each `Loop`.

**`Hyper`:** Composition threads the continuation on every step — O(1) amortised. The feedback channel is always at the head of the structure. There is no left-spine to traverse.

The transition from `Circuit` to `Hyper` via `toHyper` is the circuits equivalent of the transition from a free monad to the codensity monad in RwR — it amortises the traversal cost by making the structure maximally right-associated.

---

## Hasegawa: Cyclic Sharing vs Fixed Points

Hasegawa (1997) separates two notions that are extensionally equal but operationally different:

- **Fixed-point combinator:** `fix f = f (fix f)`. Applies `f` repeatedly. Can cause resource duplication in sharing-based implementations.
- **Trace / cyclic sharing:** Ties a cycle in the graph. The cycle is shared, not duplicated.

In `Circuit`:
- `Lift (trace k)` is the fixed-point combinator — it closes the channel immediately
- `Loop k` is cyclic sharing — the channel is held open through `Compose`

The Mendler case preserves the distinction. Without it, `Loop` becomes `Lift (trace k)` — cyclic sharing collapses to the fixed-point combinator.

**This is the remorse:** Without the Mendler case, `Loop` forgets that it is cyclic sharing. The structural information is lost. The remorse is that the interpreter produced a result — just the wrong one.

---

## The Full Hierarchy

| Structure | Naive | Efficient | Inspection |
|-----------|-------|-----------|------------|
| Monoid | list | difference list | head/tail |
| Monad | free monad | codensity monad | `viewl` |
| Category | `Cat` | `Queue` (Ran) | `viewl` on type-aligned queue |
| Traced category | `Circuit` | `Hyper` (Fix . Ran) | Mendler case in `lower` |

Each row adds one concept:
- **Monad:** adds bind (sequential dependency)
- **Category:** adds typing (typed composition)
- **Traced:** adds feedback (cyclic sharing)

Each row has the same solution shape: make the implicit structure explicit, inspect before recursing, amortise via the final encoding.

---

## Summary

The Mendler case is not a clever hack. It is the application of a well-understood principle — reflection without remorse — to traced categories.

- **Without it:** `Circuit` collapses to the free category with a fixed-point operator (degenerate model; O(n²) or worse)
- **With it:** `Circuit` is the free traced monoidal category (correct; O(n) traversal)
- **`Hyper`:** The amortised form (O(1) composition; sliding is structural)

The slogan extends: **"Two adjunctions plus one strength, amortised by the final encoding."**

**Next:** [07-future.md](07-future.md) — production use; how to extend the library; applications.

---

## References

- van der Ploeg & Kiselyov (2014) — Reflection Without Remorse
- Hasegawa (1997) — cyclic sharing vs fixed points; [hasegawa.md](../other/hasegawa.md)
- [kan-extension.md](../other/kan-extension.md) — Ran characterization and the hierarchy

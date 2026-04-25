# circuit-categorical ⟜ Categorical Reading Guide

A categorical reading guide for the `circuits` library. Each constructor and typeclass is annotated with the categorical structure it provides, so the library can be navigated in either direction: from code to theory, or from theory to code.

---

## The Two Structures

### Circuit — the free traced monoidal category

```
Circuit arr t a b
├── Category structure (free over arr)
│     Lift            ← unit of the free construction
│     Compose         ← composition (associative, unital up to laws)
│     id = Lift id    ← identity
│     ⊢ free category over arr
│
├── Profunctor structure
│     dimap f g = Compose (Lift g) (Compose f (Lift id))
│     ⊢ profunctor (contravariant a, covariant b)
│
├── Functor (covariant in b)
│     fmap f = Compose (Lift f)
│     rmap f = Compose (Lift f)
│
├── Functor (contravariant in a)
│     lmap f p = Compose p (Lift f)
│
├── Strong (via untrace)
│     untrace :: arr b c -> arr (t a b) (t a c)
│     ⊢ strength — inject into the tensor
│
├── Costrong (via trace)
│     trace :: arr (t a b) (t a c) -> arr b c
│     ⊢ costrength — close/eliminate the tensor
│
├── Monoidal (via t)
│     t :: Type -> Type -> Type
│     ⊢ monoidal product (isos inherited from meta-level (,) or Either)
│
├── Symmetric (via t)
│     swap :: t a b -> t b a
│     ⊢ implicit in the Trace instances
│
├── Traced Monoidal (the main feature)
│     Loop :: arr (t a b) (t a c) -> Circuit arr t b c
│     lower's Mendler case         ← sliding axiom
│     ⊢ free traced monoidal category over arr with tensor t
│
└── Initial Object
      lower :: Circuit arr t a b -> arr a b
      ⊢ unique traced functor out of Circuit
      ⊢ Circuit is the initial / free object
```

### Hyper — the final coalgebra

```
Hyper a b
├── Category structure
│     id = lift id
│     f . g = Hyper $ \h -> invoke f (g . h)
│     ⊢ category
│
├── Profunctor / Functor / Strong / Costrong
│     ⊢ same structure as Circuit, derived from:
│       newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
│
├── Coinductive / Corecursive
│     self-dual fixed point
│     ⊢ invoke threads the continuation bidirectionally
│
├── Traced Monoidal (structurally)
│     no explicit Loop constructor
│     sliding holds by construction in (.)
│     ⊢ traced monoidal category
│
└── Final Object
      lower    :: Hyper a b -> (a -> b)
      toHyper  :: Circuit (->) (,) a b -> Hyper a b
      triangle :: lower . toHyper = lower (on Circuit)
      ⊢ unique map *into* Hyper; Hyper is the final object
```

---

## The Two Adjunctions

The library is **two adjunctions plus one strength**. Every axiom in `other/axioms-hyp.md` collapses into one of these three ingredients.

### Adjunction 1 — Free / Forgetful

```
Lift   :: arr a b -> Circuit arr t a b      ← left adjoint (free)
lower  :: Circuit arr t a b -> arr a b      ← right adjoint (forgetful)

ε . η = id                                  ← unit-counit triangle
```

**Axioms that follow:**

```
η (f . g) = η f ⊙ η g       Lift is functorial
η id = id                   Lift preserves identity
(f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)  Compose is associative
f ⊙ η id = f = η id ⊙ f     Identity laws
```

### Adjunction 2 — Initial / Final (Galois Connection)

```
toHyper :: Circuit (->) (,) a b -> Hyper a b
flatten :: Hyper a b -> Circuit (->) (,) a b

lower . toHyper = lower     ← triangle identity
```

A **Galois connection**, not a strict adjunction. The asymmetry is real:
- Circuit is intensional — constructors are inspectable
- Hyper is extensional — only behaviour is accessible
- `toHyper . flatten ≠ id` in general

### The One Ingredient That Is Not An Adjunction Property

The **sliding axiom** is the only genuine content beyond the two adjunctions:

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

This is the **Mendler case** in `lower`. It is a strength/costrength operation on the profunctor — not derivable from free or initial-final properties. Without it, the traced structure collapses to the degenerate model. Everything else is bookkeeping.

---

## Shopping List — Where Each Property Lives

| Categorical Property | Code Location | Notes |
|---|---|---|
| **Category** | `Lift id` + `Compose` | Identity and associativity |
| **Profunctor** | `dimap f g = Compose (Lift g) … (Lift f)` | Contravariant a, covariant b |
| **Functor (covariant)** | `fmap = Compose (Lift f)` | Right action |
| **Functor (contravariant)** | `lmap f p = Compose p (Lift f)` | Left action |
| **Strong** | `Trace` typeclass: `untrace` at `(,)` | Inject into tensor |
| **Costrong** | `Trace` typeclass: `trace` at `(,)` | Eliminate tensor |
| **Choice** | `Trace` typeclass: `untrace` at `Either` | Inject choice |
| **Cochoice** | `Trace` typeclass: `trace` at `Either` | Eliminate choice |
| **Monoidal** | Tensor `t`; isos inherited from meta-level | Not modelled in GADT |
| **Symmetric Monoidal** | `swap` implicit in `Trace` instances | (,) and Either both symmetric |
| **Braided Monoidal** | Not present | (,) and Either are symmetric, not merely braided |
| **Cartesian** | Inherited from `(->)` when `arr = (->)` | Not modelled in GADT |
| **Closed Monoidal** | Not present | Would require `Curry` constructor |
| **Compact Closed** | Not at morphism level; ambient `Prof` is | Objects have duals; not in Circuit itself |
| **Traced Monoidal** | `Loop` + `Trace` typeclass + Mendler case | The main feature |
| **Free Construction** | Circuit is initial | Every traced functor factors through Circuit |
| **Final Construction** | Hyper is final | Every traced functor into Hyper is unique |

---

## Symbol Cross-Reference

```
η   ⟜  Lift      ⟜  unit of free / counit of forgetful
ε   ⟜  lower     ⟜  forgetful interpretation / reify
⊙   ⟜  Compose   ⟜  composition in the free category
↬   ⟜  Loop      ⟜  open the feedback channel
⥀   ⟜  trace     ⟜  close the feedback channel
↯   ⟜  untrace   ⟜  inject into the channel without closing
⥁   ⟜  run       ⟜  fix . ε  (compound, derived)
⊲   ⟜  push      ⟜  Compose . Lift  (compound, smart constructor)
```

Full dictionary: `~/haskell/circuits/other/symbols.md`

---

## Navigation Paths

### Code → Theory

| You are reading… | Categorical role |
|---|---|
| `Lift f` | Unit η of the free/forgetful adjunction |
| `Compose f g` | Sequential composition; free category |
| `Loop k` | Trace constructor; opens feedback channel |
| `lower` | Forgetful functor ε; unique traced functor out |
| Mendler case in `lower` | Sliding axiom; genuine traced content |
| `Hyper` | Final encoding; coinductive; self-dual |
| `toHyper` | Initial → Final; triangle identity |
| `Trace` typeclass | Costrength / cochoice on tensor t |

### Theory → Code

| You are looking for… | Where it lives |
|---|---|
| Category structure | `Lift` (embedding), `Compose` (composition), `id = Lift id` |
| Monoidal product | Tensor parameter `t` |
| Trace | `Trace` typeclass; `Loop` constructor; `trace`/`untrace` |
| Freeness | `Lift` as left adjoint; `lower` as forgetful |
| Sliding axiom | Mendler case: `lower (Compose (Loop f) g) = …` |
| Final object | `Hyper`; coinductive Church encoding |
| Universal property | `toHyper`, `flatten`; triangle `lower . toHyper = lower` |

---

## The Core Slogan

> **Two adjunctions plus one strength.**

**Adjunction 1: Free / Forgetful** (`Lift ⊣ lower`)
- Category structure, monoidal structure, functoriality
- Most of the axioms for free

**Adjunction 2: Initial / Final** (`Circuit ↔ Hyper`)
- Syntactic (Circuit) vs semantic (Hyper) representation
- Universal property tying them together
- Amortised O(1) composition in Hyper vs O(n) in Circuit

**The Sliding Axiom** (the one genuine traced content)
- `lower (Compose (Loop f) g) = trace (f . untrace (lower g))`
- Not derivable from adjunctions
- Makes the trace honest; prevents degenerate model
- Operational form of Hasegawa's naturality in X

Once these three ingredients are in place, the code shape is forced, the axioms are determined, and navigation between theory and code is systematic.

---

## Related Reading

⟜ `~/haskell/circuits/other/01-stack-language.md` — the five marks, entry point
⟜ `~/haskell/circuits/other/03-circuit.md` — free object and universal property
⟜ `~/haskell/circuits/other/04-hyper.md` — final encoding, Kan characterization
⟜ `~/haskell/circuits/other/hasegawa.md` — sliding as naturality; fixed points
⟜ `~/haskell/circuits/other/symbols.md` — symbol dictionary (single source of truth)
⟜ `~/mg/buff/learners-full.md` — compact closed via learner categories

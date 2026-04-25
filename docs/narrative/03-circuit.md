# Circuit: The Free Traced Monoidal Category

**Status:** Draft  
**Prev:** [02-gadt.md](02-gadt.md) | **Next:** [04-hyper.md](04-hyper.md)

---

`Circuit arr t a b` is the **initial object** in the (2-)category of traced monoidal categories over the base arrow `arr` with tensor `t`. This section explains what that means, why it matters, and how `lower` is the unique traced functor it implies.

---

## The GADT

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop    :: arr (t a b) (t a c) -> Circuit arr t b c
```

Three constructors. Each encodes a specific categorical structure:

| Constructor | Structure | Role |
|-------------|-----------|------|
| `Lift` | Strict monoidal functor | Embed base arrows; η of the free/forgetful adjunction |
| `Compose` | Category laws | Sequential composition; associativity and identity |
| `Loop` | Trace | Open a feedback channel; the trace constructor |

The `Category` instance is immediate:

```haskell
instance (Category arr) => Category (Circuit arr t) where
  id  = Lift id
  (.) = Compose
```

---

## The Interpreter: lower

`lower` is the unique traced functor from `Circuit` to any traced category. For the base case `arr = (->)`:

```haskell
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f)             = f
lower (Compose (Loop f) g) = trace (f . untrace (lower g))   -- Mendler case
lower (Compose f g)        = lower f . lower g
lower (Loop k)             = trace k
```

Each case corresponds to one axiom:

| Case | Axiom | What it does |
|------|-------|--------------|
| `Lift f` | `ε . η = id` | Faithful embedding; returns the base arrow unchanged |
| `Compose f g` | Associativity | Composes the two interpretations |
| `Loop k` | `ε (↬ k) = ⥀ k` | Closes the feedback channel via `trace` |
| `Compose (Loop f) g` | **Sliding** | Threads `lower g` into the channel via `untrace` before tracing |

The Mendler case is the only non-trivial one. It is the operational form of the sliding axiom — the one axiom that required `Loop`. Without it, `lower` produces the degenerate model. See [02-gadt.md](02-gadt.md).

---

## The Traced Monoidal Axioms

`Circuit` satisfies all six traced monoidal axioms (Joyal, Street & Verity 1996). The detailed proofs with `(,)` and `Either` are in [axioms-traced.md](../other/axioms-traced.md). The key structural points:

**Naturality (sliding).** The Mendler case enforces:

```
trace (f . untrace g) = trace f . g
```

This is the sliding axiom: a morphism composed on the output of a trace can be moved inside. The Mendler case reifies this as a pattern match — when a `Loop` appears at the head of a `Compose`, the right morphism is injected into the channel via `untrace` before `trace` closes it.

**Vanishing I.** `Loop (id ⊗ id) = id`. The identity feedback channel is trivial.

**Superposing.** Tensor distributes over trace as expected.

**Yanking.** In the cartesian case (`arr = (->)`, `t = (,)`), Hasegawa's Theorem 3.1 gives `run (lift f) = fix f` as a derived consequence. The trace and fixed-point operator coincide. See [hasegawa.md](../other/hasegawa.md).

---

## The Universal Property (Initiality)

`Circuit arr t` is the **initial** (free) traced monoidal category over `arr`. The universal property:

> For any traced monoidal category `C` and any (traced) functor `F : arr -> C`, there is a **unique** traced functor `F̂ : Circuit arr t -> C` making the triangle commute:
>
> ```
>     Lift
> arr -----> Circuit arr t
>  \               |
>   \          F̂  |
>    \             ↓
>     F ---------> C
> ```

`lower` is the instance of this universal property where `C = arr` and `F = id`. It is the unique traced functor from the free object back to the base.

Every traced functor out of `Circuit arr t` factors through `lower`. This is why `Circuit` is useful: **you build in `Circuit`, and any target traced category interprets it via `lower`**.

---

## The Two Adjunctions

The library encodes two adjunctions (plus one strength operation):

### Adjunction 1: Free / Forgetful

```
Lift   :: arr a b -> Circuit arr t a b      ← left adjoint (free)
lower  :: Circuit arr t a b -> arr a b      ← right adjoint (forgetful)
ε . η  =  id                                ← unit-counit triangle
```

Axioms derivable from this adjunction:

```
η (f . g) = η f ⊙ η g       (Lift is functorial)
η id = id                   (Lift preserves identity)
(f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)  (Compose is associative)
```

### Adjunction 2: Initial / Final (Galois connection)

```
toHyper :: Circuit (->) (,) a b -> Hyper a b
flatten :: Hyper a b -> Circuit (->) (,) a b
lower . toHyper = lower     -- triangle identity
```

This is a Galois connection, not a strict adjunction. The asymmetry is real: Circuit is intensional (you can inspect the constructors), Hyper is extensional (you can only observe behaviour). See [04-hyper.md](04-hyper.md).

### The Sliding Axiom: Not an Adjunction Property

The Mendler case is the one ingredient that is **not** a consequence of adjunctions:

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

This is a genuine strength/costrength operation on the profunctor, not derivable from free or initial-final properties. It is what makes the trace honest. Without it, both adjunctions are in place but the traced structure collapses.

---

## Profunctor Structure

`Circuit arr t a b` is a profunctor in `a` and `b`:

```haskell
instance Profunctor (Circuit (->) t) where
  dimap f g = Compose (Lift g) . flip Compose (Lift f)
  lmap f p  = Compose p (Lift f)
  rmap g    = Compose (Lift g)
```

The functor and applicative instances follow for `arr = (->)`:

```haskell
instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a  = Lift (const a)
  f <*> v = Lift $ \x -> reify f x (reify v x)
```

The full categorical shopping list — Strong, Costrong, Monoidal, Symmetric, Traced — is in [circuit-categorical.md](../../mg/buff/circuit-categorical.md).

---

## Ruling Out the Degenerate Model

Without the Mendler case, `Circuit` is the **free category with a fixed-point operator** — a weaker structure. The degenerate model is `H a b = a -> b`, with `Compose` as function composition and `Lift = id`. In this model, `Loop k = trace k` immediately — the feedback channel never iterates.

The Mendler case rules this out by ensuring that when a `Loop` appears on the left of a `Compose`, the right morphism participates in every iteration of the feedback. The loop structure is preserved through composition.

**One pattern match separates the free traced monoidal category from the degenerate model.**

---

## Summary

```
ε (η f)         =  f                           -- faithful embedding
ε (↬ k)         =  ⥀ k                         -- trace closes the channel
ε (↬ f ⊙ g)    =  ⥀ (f . ↯ (ε g))             -- Mendler case (sliding)
ε (f ⊙ g)      =  ε f . ε g                    -- functoriality of ε
```

Circuit is the free object. `lower` / `reify` is the unique elimination. The Mendler case is the content. Everything else follows.

**Next:** [04-hyper.md](04-hyper.md) — Hyper as the final encoding; the coinductive type; why sliding is structural there.

---

## References

- Joyal, Street & Verity (1996) — traced monoidal categories; axioms
- Hasegawa (1997) — fixed points from traces; cartesian case; [hasegawa.md](../other/hasegawa.md)
- [axioms-traced.md](../other/axioms-traced.md) — detailed proof of all six axioms
- [axioms-hyp.md](../other/axioms-hyp.md) — modern axiom presentation

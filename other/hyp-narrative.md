# The Free Traced Category and Hyperfunctions

## The Little Language

Section 7 of the 2013 paper introduces a small axiomatic language for hyperfunctions. The operations are:

```haskell
(#)  :: H b c -> H a b -> H a c
lift :: (a -> b) -> H a b
run  :: H a a -> a
(<<) :: (a -> b) -> H a b -> H a b
```

with seven axioms. Before asking what models this language, it is worth identifying what the operations are in plainer terms.

`#` is composition. `lift` embeds a plain function. `run` closes a feedback loop and extracts a value. `<<` prepends a function to a hyperfunction.

Two observations simplify things. First, `<<` is not a new primitive — it is `#` with a `lift` on the left:

```haskell
f << p  =  lift f # p
```

Axiom 6 (`lift f = f << lift f`) is then the coinductive unrolling of `lift`, and Axiom 7 becomes a statement about `#` and `run` alone. Second, Axioms 1–3 are the axioms of a category: associativity, identity, and functoriality of `lift`. They hold for any category with an embedding from functions.

What remains — Axioms 4, 5, 6, 7 — governs the interaction of `run` and `<<` with the feedback structure. These are the traced category axioms: vanishing, superposing, and sliding.

The 2013 paper notes that without `<<` and its axioms, the system has a trivial model: `H a b = a -> b`, with `#` as function composition and `lift = id`. The axioms for `<<` are precisely what rule this out.

---

## A GADT for the Axioms

The operations suggest a GADT directly. Composition and feedback are the two constructors beyond the base category:

```haskell
data TracedA arr t a b where
  Lift    :: arr a b -> TracedA arr t a b
  Compose :: TracedA arr t b c -> TracedA arr t a b -> TracedA arr t a c
  Knot    :: arr (t a b) (t a c) -> TracedA arr t b c
```

`Lift` embeds a base arrow. `Compose` is sequential composition. `Knot` opens a feedback channel: given a function that maps `(feedback, input)` to `(feedback, output)`, it closes the loop and produces a morphism `b -> c`.

The `Trace` typeclass provides the elimination:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `(->)` with `(,)`, `trace` is the arrow loop — `let (a,c) = f (a,b) in c` — and `untrace = second`. For `Either`, `trace` is `unright` — iterate until a `Right` is produced — and `untrace = fmap`.

The `Category` instance falls out immediately, and `type Traced = TracedA (->) (,)` recovers the classical `ArrowLoop` setting.

---

## The Naive Run

A first attempt at `run` follows the structure of the GADT:

```haskell
run (Lift f)      = f
run (Compose f g) = run f . run g
run (Knot k)      = trace k
```

This compiles. The types check. The Fibonacci example in the docstring:

```haskell
Knot (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
```

produces the right answer. It is easy to believe this is correct.

The equational reasoning that leads you astray is straightforward. Axiom 7 states:

```
run ((f << p) # q) = f (run (q # p))
```

Substituting `f << p = Compose (Lift f) p`:

```
run (Compose (Compose (Lift f) p) q)
= run (Compose (Lift f) p) . run q        -- by Compose case
= (run (Lift f) . run p) . run q          -- by Compose case
= f . run p . run q                        -- by Lift case
= f . run (Compose p q)                   -- backwards
```

And the RHS:

```
f (run (Compose q p))
= f . run (Compose q p)
= f . (run q . run p)
```

These are equal only if `run p . run q = run q . run p` — that is, only if the two morphisms commute. This is not true in general. The naive run fails Axiom 7.

The Fibonacci example did not catch this because it has no `Compose` wrapping a `Knot` on the left. It tests `Knot` in isolation, which the naive run handles correctly. The failure only surfaces when something is composed after a feedback loop — when `run` needs to slide a morphism inside the trace.

---

## The Sliding Axiom

The nLab statement of sliding is:

```
tr^X((id_B x g) . f) = tr^Y(f . (id_A x g))
```

In plain terms: if you have a morphism `g` composed on the output side of a trace, it can be moved to the input side instead. The trace is natural in its feedback object.

The naive run produces `trace f . run g` for `Compose (Knot f) g` — `run g` is applied first, then the trace closes. Sliding requires `run g` to be applied *inside* the feedback channel, so it participates on every pass through the loop, not just at entry.

For `(,)` this distinction is invisible when the loop terminates in one step. For `Either`, where the loop iterates until a `Right` is produced, `run g` applied once at entry versus on every pass gives different results. The naive run silently gives the wrong answer.

---

## The Mendler Inspection

The fix is a single pattern match added to `run`:

```haskell
run :: (Category arr, Trace arr t) => TracedA arr t x y -> arr x y
run (Lift f)             = f
run (Compose (Knot f) g) = trace (f . untrace (run g))
run (Compose f g)        = run f . run g
run (Knot k)             = trace k
```

When a `Knot` appears on the left of a `Compose`, `run g` is extracted and injected into the feedback channel via `untrace` before being handed to `trace`. For `(,)` this is `second (run g)` — applying `run g` to the second component. For `Either` it is `fmap (run g)` — mapping over the `Right` branch.

The order of pattern matches is load-bearing. Without the `Compose (Knot f) g` case appearing before the general `Compose` case, it falls through and produces the naive — incorrect — behaviour.

This is the Mendler algebra step: inspecting one level of the syntax tree before recursing, rather than processing subterms independently. It is not optional. Without it, `Knot` is observationally equivalent to `Lift (trace k)` — the feedback channel closes immediately, the loop structure is lost, and `TracedA` collapses to the free category with a fixed-point operator. This is the degenerate model the 2013 paper warns about.

---

## Hyperfunctions as the Final Encoding

`TracedA` is the initial encoding — a syntax tree whose `run` enforces the axioms. Hyperfunctions are the final encoding — a coinductive type whose structure *is* the axioms.

```haskell
newtype HypA arr a b = HypA {ι :: arr (HypA arr b a) b}
```

Composition:

```haskell
f ⊙ g = HypA $ \h -> ι f (g ⊙ h)
```

The backwards channel `h :: HypA arr b a` is where the feedback lives. In `TracedA`, a `Knot` explicitly opens a feedback channel. In `HypA`, every morphism already has one — the continuation argument `HypA arr b a` is structurally present in every value. `Knot` does not go anywhere; it dissolves into the type.

The sliding axiom in `HypA` is not enforced by inspection — it is inherent in `⊙`. The continuation `h` is threaded through `g ⊙ h` before `ι f` sees it, on every unfolding. There is no degenerate model to fall into because the type itself encodes the feedback structure.

The map from syntax to semantics:

```haskell
toHyp :: Traced a b -> Hyp a b
toHyp (Lift f)        = rep f
toHyp (Compose f g)   = toHyp f ⊙ toHyp g
toHyp (Knot k)        = trace k
```

where `trace` is the `Trace Hyp (,)` instance. This is the unique traced functor from the initial object into `Hyp`, given by the universal property of `TracedA`. It does not need a Mendler case because `⊙` already satisfies sliding.

The other direction is the forgetful map:

```haskell
fromHyp :: Hyp a b -> Traced a b
fromHyp h = Lift (lower h)
```

`lower` observes the hyperfunction against a constant continuation, collapsing it to a plain function. All feedback structure is lost. `fromHyp` is not an inverse to `toHyp` — it is the observation that `Hyp` can only be seen from the outside.

The triangle closes: `lower . toHyp = run`. Mapping `Traced` into `Hyp` and then observing gives the same result as running `Traced` directly.

---

| | `TracedA` | `Hyp` |
|---|---|---|
| Encoding | Initial (syntax) | Final (semantics) |
| Sliding | Enforced by Mendler inspection | Inherent in `⊙` |
| Feedback | Explicit `Knot` constructor | Structural in `HypA` type |
| Degenerate model | Possible without Mendler case | Not possible |
| Map to `(->)` | `run` | `lower` |

The one-line change to `run` — adding the `Compose (Knot f) g` case — is the difference between `TracedA` being a free traced category and being the free category with a fixed-point operator. The Mendler inspection is what keeps `Knot` distinct from `Lift`.

---

## The Tensor is a Parameter

`TracedA arr t a b` abstracts over the tensor `t`. Both instances give valid traced categories and both support `toHyp`:

| Tensor `t` | `trace`    | `untrace` | Operational character           |
|------------|------------|-----------|---------------------------------|
| `(,)`      | `unsecond` | `second`  | Lazy product knot; simultaneous |
| `Either`   | `unright`  | `fmap`    | While-loop; sequential handoff  |

`Hyp` is neutral to this choice — the feedback channel type does not appear in the `HypA` newtype. `toHyp` works for both tensors. The choice of tensor determines the operational behaviour of feedback, not the categorical structure.

**Costrong / `(,)`:** feedback and output exist in parallel. Both sides progress lock-step. Suitable for dataflow, zipping, true concurrency. The trace is `unsecond` — close the loop on the second component, return the first.

**Cochoice / `Either`:** sequential handoff — taking turns. Only one participant acts per step. Suitable for coroutines, schedulers, state machines. The trace is `unright` — iterate until a `Right` is produced.

Hyperfunctions (Kidney-Wu 2026) unify these patterns as communicating continuations. The choice of tensor determines whether communication is simultaneous or alternating. `TracedA` makes this choice parametric; classical `Traced = TracedA (->) (,)` defaults to the Costrong setting that matches the original hyperfunction newtype.

---

## Co is the (,)-Traced Channel

```haskell
type Channel i o a = Hyp (o -> a) (i -> a)

newtype Co r i o m a = Co
  { route :: (a -> Channel (m r) i o) -> Channel (m r) i o }
```

`Co` is a `Hyp`-based coroutine where input and output are simultaneous — one continuation handles both directions. This corresponds to the `(,)` tensor: both channels exist at once, connected through the `Hyp` duality. The `Channel` type is exactly a hyperfunction between two function spaces, making the bidirectional communication structure explicit.

---

## The Kan Extension

The Icelandjack observation (hyperfunctions issue #3, 2017):

```
Hyper a b = Fix (Ran (Const a) (Const b))
```

`HypA` is not just any hyperfunction implementation — it is the right Kan extension `Ran (Const a) (Const b)`. The continuation `HypA b a` represents the most general way to convert from `Const a` to `Const b`.

This explains the Mendler inspection: the `Compose (Knot f) g` case in `run` is exactly what Kan extension naturality requires. The sliding law is not an implementation trick — it is enforcing the naturality condition of the Kan extension.

The degenerate model impossibility also follows: since `HypA` is a Kan extension, it cannot collapse to `a -> b` without violating the universal property.

The unification:

```
TracedA a b  ~  Free (Ran (Const a) (Const b))
```

`TracedA` (initial) and `HypA` (final) are related by the Kan extension adjunction. `ι` is the counit of the adjunction. The triangle `lower . toHyp = run` is the unit-counit identity.

---

## Deforestation and GHC Erasure

`HypA` is the Church encoding of `TracedA`. The same move as Church-encoded lists
vs cons cells — and GHC's simplifier can fuse away the intermediate structure entirely
under `{-# INLINE #-}` on `ι`, `⊙`, `run`, `toHyp`.

The axiom equations are exactly the rewrite rules GHC needs:

```
Compose (Lift id) f   ~   f          -- identity fusion, Lift id node never allocated
Compose f (Compose g h) ~ Compose (Compose f g) h  -- associativity, tree shape irrelevant
run (Compose (Knot f) g) = trace (f . untrace (run g))  -- Mendler: the critical fusion rule
```

Without the Mendler case, `Knot` doesn't fuse — it's buried under left-nested `Compose`
and pays constructor allocation at every feedback point. With it, the feedback channel is
a lazy function rather than a heap object.

The quotient `TracedA / axioms` is not just a mathematical nicety. The axiom equations
are the fusion rules. `HypA` makes them structural: under inlining the newtype wrapper
disappears, `⊙` becomes direct function composition, and the traced structure costs
nothing at runtime. Perfect deforestation — same guarantee as `build`/`foldr` stream
fusion in `Data.List`, extended to the feedback case by the addition of `Fix`.

# Hyp and TracedA: The Bridge

**Sources:** LKS (Launchbury, Krstic & Sauerwein 2013), Kidney-Wu 2026, JSV (Joyal, Street & Verity 1996), Hasegawa 1997

---

## The claim

`Hyp` and `TracedA` are the same structure arrived at from opposite directions.

- LKS started from streams and coroutines, derived seven axioms, and found a feedback constructor was needed.
- The categorical approach starts from traced monoidal category axioms and arrives at the same three GADT constructors.
- They meet at: **Axiom 7 = Sliding = Knot**.

---

## Operator dictionary

| LKS 2013       | Kidney-Wu 2026 | TracedA          | Role                        |
|----------------|----------------|------------------|-----------------------------|
| `f # g`        | `f ⊙ g`        | `Compose f g`    | Sequential composition      |
| `lift f`       | `rep f`        | `Lift f`         | Embed base arrow            |
| `f << h`       | `f ⊲ h`        | `Compose (Lift f) h` | Prepend function        |
| `run`          | `run`          | `run`            | Eliminate / tie knot        |
| _(implicit)_   | _(implicit)_   | `Knot k`         | Feedback constructor        |
| `lower`        | `lower`        | `run`            | Interpret to base arrow     |

`<<` is not primitive: `f << h = Compose (Lift f) h`. Axiom 6 (`lift f = f << lift f`) is then the coinductive unrolling of `Lift` under `Compose`.

---

## Axiom correspondence

JSV work in a balanced monoidal category (braids, twists). Hasegawa and LKS both specialise to symmetric monoidal categories. The narrative lives in the symmetric/cartesian case throughout; Hasegawa's specialisation is the right landing point.

| LKS Axiom | JSV / Hasegawa counterpart | TracedA location | Notes |
|-----------|---------------------------|------------------|-------|
| 1: `(f # g) # h = f # (g # h)` | Monoidal associativity | `Category` instance | Pre-condition, not a trace axiom |
| 2: `f # self = f = self # f` | Monoidal unit / Vanishing I | `Lift id` | `self = lift id` is identity |
| 3: `lift (f . g) = lift f # lift g` | Functor law for embedding | `Lift` | Strict monoidal functor |
| 4: `run (lift f) = fix f` | Yanking (cartesian specialisation) | `run (Knot ...)` | In cartesian case, trace induces `fix` |
| 5: `(f << p) # (g << q) = (f.g) << (p # q)` | Superposing | `Compose` + `Lift` | `<<` encodes feedback channel |
| 6: `lift f = f << lift f` | Vanishing II / coinductive unfolding | `Lift` under `Compose` | Loop unrolling as `Tr^{XxY} = Tr^X . Tr^Y` |
| 7: `run ((f << p) # q) = f (run (q # p))` | **Sliding** (Left Tightening) | `run (Compose (Knot f) g)` | The core axiom; demands `Knot` |

JSV derives naturality from the natural family structure. Hasegawa makes it explicit as Left and Right Tightening. nLab names all five: vanishing I, vanishing II, superposing, yanking, naturality. LKS Axiom 7 is the sliding/naturality axiom in the concrete hyperfunction setting.

**What the 2013 presentation omits:** Vanishing I is absorbed into Axiom 2 via `self`. Right Tightening is not stated separately. The 2013 presentation is more economical, trading categorical generality for a Haskell-friendly form.

---

## Axiom 7 is the sliding axiom is Knot

The restated Axiom 7 (factoring out `fix` via `run = fix . lower`):

```
lower ((f << p) # q) = f . lower (q # p)
```

Expanding with `f << p = Compose (Lift f) p` and `# = Compose`:

```
lower (Compose (Compose (Lift f) p) q) = f . lower (Compose q p)
```

LHS reduces to `f . lower p . lower q`.
RHS reduces to `f . lower q . lower p`.

These are equal only when the feedback channel is existentially hidden inside a knot — when `lower p` and `lower q` share a cyclic state `s` that routes through `unfirst`. This is exactly `Knot`:

```haskell
Knot :: arr (t a b) (t a c) -> TracedA arr t b c
run (Knot k) = trace k
run (Compose (Knot f) g) = trace (f . untrace (run g))   -- sliding rule
```

The sliding rule in `run` is Axiom 7 made computational. Without `Knot`, the free category built from `Lift` and `Compose` alone cannot satisfy Axiom 7 — it has no feedback, and `lower p . lower q` never commutes with `lower q . lower p` in general.

---

## toHyp is the homomorphism

```haskell
toHyp :: Traced a b -> Hyp a b
toHyp (Lift f)      = rep f
toHyp (Compose f g) = toHyp f ⊙ toHyp g
toHyp (Knot k)      = trace (rep k)
```

`Lift` and `Compose` map trivially. `Knot` maps to `trace . rep` — lift the base arrow into `Hyp` and apply the trace immediately. This is where the feedback is consumed. `toHyp` is a homomorphism because `Hyp` already satisfies all the traced axioms; the sliding rule does not need to be re-enforced.

`Hyp` is a model of `TracedA` where `trace` and `run` collapse into one operation. In `TracedA` they are distinct: `run` is the interpreter, `trace` is the categorical operation. In `Hyp`, the self-referential definition `run h = ι h (HypA run)` means they are the same.

---

## The tensor is a parameter

`TracedA arr t a b` abstracts over the tensor `t`. Both instances give valid traced categories and both support `toHyp`:

| Tensor `t` | `trace`    | Operational character        | Categorical name |
|------------|------------|------------------------------|------------------|
| `(,)`      | `unsecond` | Lazy product knot; simultaneous | Costrong / coinductive |
| `Either`   | `unright`  | While-loop; sequential handoff | Cochoice / inductive  |

`Hyp` is neutral to this choice — the feedback channel type does not appear in the `Hyp` newtype. `toHyp` works for both tensors.

---

## Hasegawa's cartesian specialisation

In a cartesian traced category, Hasegawa's Theorem 3.1 establishes that the trace is equivalent to a fixed-point operator satisfying the Conway axioms. This is why `run (lift f) = fix f` (LKS Axiom 4) is not an arbitrary choice — in the cartesian setting, any trace necessarily induces `fix`. The connection is a theorem, not a definition.

Hasegawa also separates cyclic sharing (the trace) from fixed-point combinators: they agree extensionally but differ operationally. The fixed-point combinator can cause resource duplication in sharing-based implementations; the trace does not. This maps onto the `Costrong` vs `Cochoice` distinction: not just a design preference but a semantic difference with operational consequences.

---

## Open questions

- The precise isomorphism between `Proxy`/`streaming` types and `TracedA` is not established.
- The Geometry of Interaction connection (Int(C) completion, `callCC`, shift/reset) is a conjecture not yet developed.
- The graded structure counting `Knot` depth and its implications for Okasaki queue methods are noted but not formalised.
- Kidney-Wu 2026: specific examples (breadth-first search via Hofmann, concurrency scheduler) mapping onto `TracedA`/`HypA` would strengthen "hyperfunctions are traced catamorphisms."

---

## The Kan Extension Hierarchy

The free-category package makes the pattern explicit for the free category:

```haskell
-- Initial: lists of composable morphisms
data Cat f a b where
  Id   :: Cat f a a
  (:.) :: f b c -> Cat f a b -> Cat f a c

-- Final: Cayley/Yoneda embedding
newtype Queue f a b = Queue { runQueue :: forall r. Cat f b r -> Cat f a r }
```

`Queue f a b` is `Ran (Cat f) (Cat f)` — the free category represented via its
universal property rather than as explicit lists. Same category, O(1) amortised
composition instead of O(n).

Adding `Knot` (the trace) to the free category requires a fixpoint, because feedback
loops back on itself. The same Cayley move applied to the free *traced* category
gives `HypA`:

```haskell
HypA a b  =  HypA b a -> b    -- Fix (Ran (Const a) (Const b))
```

The hierarchy:

| Level              | Initial (syntax)  | Final (semantics) | What the step adds |
|--------------------|-------------------|-------------------|--------------------|
| Free category      | `Cat` / `LiftCompose` | `Queue`       | Yoneda / Ran       |
| Free traced category | `TracedA`       | `HypA`            | Fix (feedback)     |

`Queue` is `Ran` of the free category along itself. `HypA` is `Fix(Ran(Const a)(Const b))` — the `Fix` is exactly what `Knot` contributes. Feedback requires a fixpoint; the free category does not.

The universal property stated categorically: for any traced monoidal category `C`
and functor `F : arr -> C`, there is a unique traced functor `TracedA arr t -> C`
extending `F`. When `C = HypA`, that unique functor is `toHyp`. `HypA` is the
codensity/Yoneda representation of `TracedA` with the feedback baked into the type
rather than sitting as an explicit constructor.

The triangle `lower . toHyp = run` is the unit-counit identity of this adjunction:
`run` eliminates the initial encoding, `lower` observes the final encoding, and they
agree because they are the same universal map viewed from opposite sides.

---

## Reflection without Remorse: The Traced Category Extension

**Reference:** van der Ploeg & Kiselyov, Haskell 2014

The paper establishes a hierarchy for solving the build-and-observe performance
problem:

| Structure | Naive       | CPS / Codensity | Explicit sequence     |
|-----------|-------------|-----------------|----------------------|
| Monoid    | list        | difference list | queue                |
| Monad     | free monad  | codensity monad | type-aligned queue   |
| Category  | `Cat`       | `Queue` (Ran)   | type-aligned queue   |

The paper stops at categories. The natural next row is:

| Traced category | `TracedA` | `HypA` (Fix . Ran) | type-aligned queue + Fix |

### The direct mappings

**Left-nested composition.** Left-nested `>>=` in the paper produces O(n²)
performance. Left-nested `Compose` in `TracedA` produces the same problem — and
worse, without the Mendler case, `Knot` gets buried under the left-nesting and
collapses to the degenerate model.

**The hidden sequence.** The paper's title refers to the implicit sequence of
monadic binds, made explicit by a type-aligned queue. In `TracedA`, the hidden
structure is the feedback channel inside `Knot`. Both are made explicit by the
respective constructions: the queue in the paper, the `Knot` constructor here.

**`PMonad` and `Trace`.** The paper introduces `PMonad`, an alternative to `Monad`
where bind takes an explicit type-aligned sequence as its right argument rather than
a single continuation:

```haskell
class PMonad m where
  return' :: a -> m a
  (>>^=) :: m a -> MCExp m a b -> m b
```

This is structurally the same move as the `Trace` class: instead of hiding the
feedback channel inside the monad, make it an explicit typed argument:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- observe the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into the channel
```

`untrace` is the analogue of `expr = tsingleton` in the paper — converting a single
morphism into the explicit sequence representation. `trace` is the analogue of `val`
— observing the head of the sequence and reducing.

**`viewl` is the Mendler case.** The paper's solution requires `viewl` on the
type-aligned queue to inspect the head of the sequence before recursing. In `run`,
the Mendler case does exactly this:

```haskell
run (Compose (Knot f) g) = trace (f . untrace (run g))
```

When a `Knot` appears at the head of a composition, inspect it before recursing into
`g`. Without this case, `run` falls through to the general `Compose` rule, buries the
`Knot`, and produces the degenerate model — the traced category collapses to the free
category with a fixed-point operator. This is the remorse: `Knot` becomes
observationally equivalent to `Lift (trace k)`.

### The step the paper does not take: Fix

The paper notes that free monoids are free categories with one object, and free
categories are paths through a directed graph — type-aligned sequences. It does not
take the next step.

The free traced category requires one addition beyond the free category: a fixpoint.
`Knot` is the generator of feedback, and `HypA = Fix(Ran(Const a)(Const b))` is the
efficient (final/codensity) representation of the free traced category — exactly as
`Queue` is the efficient representation of the free category.

```
Cat  +  viewl  =  Queue         -- reflection without remorse for categories
TracedA  +  Mendler  =  HypA    -- reflection without remorse for traced categories
```

The `Fix` in `HypA` is what `Knot` contributes. Every other step — making the
sequence explicit, using Ran for efficient composition, inspecting before recursing —
is present in both. The traced case adds one thing: the feedback loop closes on
itself, requiring a fixpoint the free category never needs.

### The full hierarchy

| Structure       | Naive     | Efficient (Ran / Fix.Ran) | Inspection mechanism     |
|-----------------|-----------|---------------------------|--------------------------|
| Monoid          | list      | difference list            | head/tail                |
| Monad           | free monad| codensity monad            | `viewl` on TCQueue       |
| Category        | `Cat`     | `Queue`                    | `viewl` on type-aligned queue |
| Traced category | `TracedA` | `HypA`                     | Mendler case in `run`    |

Each row adds one capability over the previous. The traced row adds `Fix` — the
ability to close a feedback loop. The Mendler inspection is what keeps that loop
visible rather than flattening it into the layer below.

---

## Costrength: The Categorical Backing for Trace

**Reference:** Balan & Pantelimon, "The Hidden Strength of Costrong Functors" (2025)

The `Trace` typeclass bundles two directions of a monoidal action:

```haskell
class Trace arr t where
  untrace :: arr b c -> arr (t a b) (t a c)   -- STRONG:   push action inside
  trace   :: arr (t a b) (t a c) -> arr b c   -- COSTRONG: pull action out
```

This is the formal definition of an M-costrong functor. The paper's costrength natural
transformation `cst : F(M . X) -> M . F(X)` is exactly `trace`. The strength `st :
M . F(X) -> F(M . X)` is exactly `untrace`.

### Theorem 3.2: Costrong = Copointed on cartesian categories

On a cartesian category, costrong endofunctors are in bijection with copointed
endofunctors — those equipped with a natural transformation `ε : F -> id`. The
costrength `cst` corresponds to `ε` via:

```
ε : F(M) -> M    given by    F(M) ≅ F(M x 1) -> M x F(1) -> M
```

For our `trace`: the copoint `ε` is exactly the operation that extracts a plain arrow
from a traced one. `trace` is the copoint of the traced structure.

### Proposition A.4: Free constructions inherit costrength

If the generating functor `F` is M-costrong, so is the free monad on `F`. `TracedA` is
the free traced category over `arr`. If `arr` supports `Trace` (is costrong with respect
to `t`), then `TracedA` inherits it. This is the categorical justification for why the
`Trace` instance on `TracedA` is well-defined and not just ad hoc.

### Section 4.2: Costrength and streams

A costrong functor `F` lifts to stream coalgebras: `cst : F(M x X) -> M x F(X)` keeps
the output channel observable through the context `F`. For `Either` tensor, this is
exactly the while-loop trace — `Right` (the output) remains extractable from within `F`
on every iteration. The stream lifting result formally backs the `Trace (->) Either`
instance as a valid costrength.

### The optics connection

Section 4.1: an M-costrong functor paired with an M-strong functor gives an optics
transformer. Our `(trace, untrace)` pair is this exactly — `trace` costrong, `untrace`
strong. Together they define the traced optic structure, and this is the formal backing
for the profunctor instances (`Costrong`, `Strong`, `Cochoice`, `Choice`) on `TracedA`.

The `Trace` typeclass is not an ad hoc design — it is the interface of a costrong/strong
adjoint pair, formalised independently in the optics literature.

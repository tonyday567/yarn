# yarn: tracing hyperfunctions

**The foundation:** TracedA (initial), HypA (final), and their adjunction

| Component               | Location      | Role                              | Status |
|-------------------------|---------------|-----------------------------------|--------|
| **TracedA**             | src/Traced.hs | Free traced category (GADT)       |        |
| **HypA**                | src/Hyp.hs    | Church Encoding of TracedA        |        |
| **run = lower . toHyp** |               | The Traced adjunction             |        |
| **Kan extension**       |               | TracedA = Ran (Const a) (Const b) |        |
| narrative               | readme.md     |                                   |        |

**The axioms:** Traced monoidal category semantics

Action: [axioms-traced.md](other/axioms-traced.md) — JSV axioms with proofs
Action: [axioms-hyp.md](other/axioms-hyp.md) — Kidney Wu axioms with proofs

# The Free Traced Category and Hyperfunctions

## references
- Joyal, Street & Verity, "Traced monoidal categories" (Math. Proc. Camb. 1996)
- Hasegawa, "Recursion from cyclic sharing: traced monoidal categories" (1997)
- Launchbury, Krstic & Sauerwein, "Lazy functional reactive programming" (JFP 2013)
- Kidney & Wu, "Hyperfunctions and the monad of streams" (2026)
- Balan & Pantelimon, "The hidden strength of costrong functors" (2025)
- van der Ploeg & Kiselyov, "Reflection without remorse" (Haskell 2014)

Action: nlab reference included. 2003 paper. Anything in ~/self/yarn

## The Little Language

Section 7 of LKS paper introduces a small axiomatic language for hyperfunctions. The operations are:

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

Right Kan extensions (Ran): For F : C → D along K : C → E, the right Kan extension `Ran K F : E → D` is characterized by a universal property: it's the terminal object among functors G with a natural transformation τ : F ⇒ G ∘ K.

The key operation is the **counit**: `ε : Ran K F ∘ K ⇒ F`, which extracts the result.

If `TracedA a b ~ Ran (Const a) (Const b)`, then:

- The embedding `Lift : (a → b) → TracedA a b` is K
- The counit is the operation that recovers `(a → b)` from the Ran structure
- That counit is `run`

## The Mendler Case as Counit Naturality

The Mendler case in `run`:

```haskell
run (Compose (Knot f) g) = trace (f . untrace (run g))
```

enforces naturality of the counit with respect to composition.

When a Knot appears at the head of a Compose, you must inspect it first to satisfy the universal property — otherwise the counit doesn't commute.

Without this case, the universal property is violated: `Knot` collapses to the degenerate model.

Ran K F as an end is:
Ran K F x = ∫_c Hom(K c, x) → F c
Substituting K = Const a, F = Const b:
Ran (Const a) (Const b) x = ∫_c Hom(Const a c, x) → Const b c
                           = ∫_c Hom(a, x) → b
                           = Hom(a, x) → b
The end over c vanishes because neither Const a c nor Const b c depend on c. So:
Ran (Const a) (Const b) x = (a -> x) -> b
Which is a continuation — give me a function from a to the answer type x, and I'll give you a b.

Now Fix of that functor would be:

HypA a b  =  Fix (Ran (Const a) (Const b))

where:

Ran (Const a) (Const b) x  =  (a -> x) -> b       -- end formula, c vanishes

Fix ties the knot on x, replacing it with the whole type flipped:

Fix (Ran (Const a) (Const b))  =  (Fix (Ran (Const b) (Const a)) -> b)
                                =  (HypA b a -> b)
                                =  HypA a b
The fixpoint is the self-referential duality: to produce a b you invoke your own dual HypA b a. The Ran gives you the continuation structure, the Fix gives you the knot.


So the question is whether Traced a b ~ Ran (Const a) (Const b) is established precisely enough to support that chain of reasoning. If it is, then Hyp a b ~ Fix (Traced a b) would be a theorem, and toHyp would be the algebra map — which is close to but not quite the same as saying toHyp is Fix.


## Open Work

⟝ Prove that the Mendler case in `run` is exactly the counit naturality of `Ran(Const a)(Const b)`, formalized.
⟝ The research direction: not "what is HypA," but "what does the Ran structure force about how we interpret it."

The unification:

```
TracedA a b  ~  Free (Ran (Const a) (Const b))
```

ι⟝ prove the following statement, or ptherwise: `TracedA` (initial) and `HypA` (final) are related by the Kan extension adjunction. `ι` is the counit of the adjunction. The triangle `lower . toHyp = run` is the unit-counit identity.

```haskell
toHyp :: Traced a b -> Hyp a b
toHyp (Lift f)      = rep f
toHyp (Compose f g) = toHyp f ⊙ toHyp g
toHyp (Knot k)      = trace (rep k)
```

`Lift` and `Compose` map trivially. `Knot` maps to `trace . rep` — lift the base arrow into `Hyp` and apply the trace immediately. This is where the feedback is consumed. `toHyp` is a homomorphism because `Hyp` already satisfies all the traced axioms; the sliding rule does not need to be re-enforced.

`Hyp` is a model of `TracedA` where `trace` and `run` collapse into one operation. In `TracedA` they are distinct: `run` is the interpreter, `trace` is the categorical operation. In `Hyp`, the self-referential definition `run h = ι h (HypA run)` means they are the same.


---

## HypA is a Church encoding just like Codensity. 

⟝ integrate reflection without remorse reading.

`HypA` is the Church encoding of `TracedA`. The same move as Church-encoded lists
vs cons cells — and GHC's simplifier can fuse away the intermediate structure entirely
under `{-# INLINE #-}` on `ι`, `⊙`, `run`, `toHyp`.

The axiom equations are exactly the rewrite rules GHC needs:

```
Compose (Lift id) f   ~   f          -- identity fusion, Lift id node never allocated
Compose f (Compose g h) ~ Compose (Compose f g) h  -- associativity, tree shape irrelevant
run (Compose (Knot f) g) = trace (f . untrace (run g))  -- Mendler: the critical fusion rule
```


# Hyp and TracedA: The Bridge

**Sources:** LKS (Launchbury, Krstic & Sauerwein 2013), Kidney-Wu 2026, JSV (Joyal, Street & Verity 1996), Hasegawa 1997

---

## The claim

`Hyp` and `TracedA` are the same structure arrived at from opposite directions.

- LKS started from streams and coroutines, derived seven axioms, and found a feedback constructor was needed.
- The categorical approach starts from traced monoidal category axioms and arrives at the same three GADT constructors.
- They meet at: **Axiom 6 = Sliding = Knot**.

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

## Axiom 6 is the sliding axiom is Knot

The restated Axiom 6 (factoring out `fix` via `run = fix . lower`):

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

```
Cat  +  viewl  =  Queue         -- reflection without remorse for categories
TracedA  +  Mendler  =  HypA    -- reflection without remorse for traced categories
```

### The full hierarchy

| Structure       | Naive     | Efficient (Ran / Fix.Ran) | Inspection mechanism     |
|-----------------|-----------|---------------------------|--------------------------|
| Monoid          | list      | difference list            | head/tail                |
| Monad           | free monad| codensity monad            | `viewl` on TCQueue       |
| Category        | `Cat`     | `Queue`                    | `viewl` on type-aligned queue |
| Traced category | `TracedA` | `HypA`                     | Mendler case in `run`    |

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


# circuits: tracing hyperfunctions

A `Circuit` is a GADT and is the free traced monoidal category over an arrow, with a choice of a trace operation associated with the tensor of the category.

``` haskell
Circuit arrow tensor a b 
```

A hyperfunction (Hyp) is the Church encoding of a Circuit and, as such, might represent an efficient and performant target for broad classes of computation requiring tensor elimination, such as resource acquisition, parsing, backpropogation and tensor calculii of all manner. 

## narrative coverage

This narrative covers foundational content for understanding the library, written here in development form.

Circuit ⟜ Circuit arrow tensor a b ⟜ Free traced category GADT
Hyp ⟜ Hyperfunction ⟜ Church encoding of Circuit 
The trace adjunction ⟜ `lower . unfold = run`
Kan extension ⟜ `Circuit arrow tensor a b = Ran (Const a) (Const b)` 

axioms ⟜ circuit and hyperfunction semantics
- [axioms-traced.md](other/axioms-traced.md) — nlab axioms with proofs
- [axioms-hyp.md](other/axioms-hyp.md) — Kidney–Wu axioms with proofs

## References

⟝ nlab reference here

- Joyal, Street & Verity, "Traced monoidal categories" (Math. Proc. Camb. 1996)
- Hasegawa, "Recursion from cyclic sharing: traced monoidal categories" (1997)
- Launchbury, Krstic & Sauerwein, "Hyperfunctions" (2013) (LKS)
- Kidney & Wu, "Hyperfunctions and the monad of streams" (2026) (KW)
- Balan & Pantelimon, "The hidden strength of costrong functors" (2025)
- van der Ploeg & Kiselyov, "Reflection without remorse" (2014) (RwR)

---

## A little Language

Section 7 of LKS introduces a small axiomatic language for hyperfunctions with the following operatots and axioms.

### semantics

Over an abstract type, the semantics (operations, interpretations, implementations) are composing, lifting, running and prepending.

```haskell
(#)  :: H b c -> H a b -> H a c
lift :: (a -> b) -> H a b
run  :: H a a -> a
(<<) :: (a -> b) -> H a b -> H a b
```

⟝ switch to modern unicode.

### axioms

axiom 1 ⟜ associativity ⟜ `(f # g) # h = f # (g # h)`
axiom 2 ⟜ lifted identity ⟜ `f # lift id = f = lift id # f`
axiom 3 ⟜ lift is a functor ⟜ `lift (f . g) = lift f # lift g`
axiom 4 ⟜ run is fixed-point ⟜ `run (lift f) = fix f`
axiom 5 ⟜ prefix composition ⟜ `(f << p) # (g << q) = (f . g) << (p # q)`
axiom 6 ⟜ run with prefix ⟜ `run ((f << p) # q) = f (run (q # p))`

### free category

The first three axioms; associativity, identity and functorality of lift are the axioms that construct a free category, out of lift and (#).

### lift

LKS has seven axioms listed but this includes the lift equation which is classified instead as a semantic:

```haskell
lift :: (a → b) → (a ↬ b)
lift f = f << lift f
```

Lifting into Hyp constructs hyperfunctions by repeatedly applying `<<` under lazy evaluation. KW characterise this operator as a `push`, LKS as a left action prepend.

## (<<) is a compound semantic.

⟝ motivation for completeness and simpleness (universal properties?)

(<<) is not a primitive operator. It can be split into lifting and composing.

```haskell
f << p  =  lift f # p
```

`lift f = f << lift f` is then a coinductive unrolling of `lift`.

## run is a compound semantic.

run :: H a a -> a 

can be thought of as doing two things:

lower ⟜ transforming a H a b to an ordinary function. ⟜ lower :: H a b -> (a -> b)
fix ⟜ tie the fixpoint ⟜ fix :: (a -> a) -> a ⟜ fix f = f (fix f)

So run can be decomposed:

``` haskell
run = fix . lower
```

## simplifications

Substituting `f << p = lift f # p` and `run = fix . lower` rewrites axioms 4, 5 and 6.

### axiom 4 — faithfulness

``` haskell
run (lift f) = fix f
fix (lower (lift f)) = fix f

-- under fixpoint conditions:
lower (lift f) = f
lower . lift = id
```

Axiom 4 becomes the unit of an adjunction between hyperfunctions and ordinary
functions: `lower` is left inverse to `lift`. The embedding is faithful — lifting a
function and then observing it returns exactly what you started with. This is a
conservativity condition, not a constructor: it constrains interpretation, it does
not add structure.

### axiom 5 — centrality of lifted arrows

``` haskell
(f << p) # (g << q) = (f . g) << (p # q)

-- substituting f << p = lift f # p:
(lift f # p) # (lift g # q) = lift (f . g) # (p # q)
```

The right side reduces by associativity and functoriality of `lift`:

```
lift (f . g) # (p # q)  =  (lift f # lift g) # (p # q)   -- axiom 3
                        =  lift f # (lift g # (p # q))   -- axiom 1
```

The left side by associativity:

```
(lift f # p) # (lift g # q)  =  lift f # (p # (lift g # q))   -- axiom 1
```

Cancelling `lift f #`, axiom 5 reduces to:

``` haskell
p # (lift g # q) = lift g # (p # q)
```

**Lifted arrows are central** — they slide past any hyperfunction under composition.
This is not derivable from axioms 1 and 3; it is an independent property of how
`lift` embeds into `#`. Categorically it is the symmetric braiding: pure arrows
carry no feedback channel to obstruct a swap, so they commute past everything. A
non-braided setting would require an explicit `Braid` constructor to state this.

### axiom 6 — feedback

Substituting `run = fix . lower` and cancelling `fix` (which appears uniformly on
both sides), then substituting `<<`:

``` haskell
run ((f << p) # q) = f (run (q # p))
fix (lower ((f << p) # q)) = f (fix (lower (q # p)))
lower ((f << p) # q) = f . lower (q # p)
lower ((lift f # p) # q) = f . lower (q # p)
```

The `q # p` on the right is a swap of `p` and `q`, not just reassociation. Axiom 6
is not commutativity — it is the sliding axiom of a traced monoidal category,
applied to a `lift f` that carries a hidden feedback channel threaded through both
`p` and `q`. The channel is implicit: it lives in the way `run` ties the knot.

### axiom categorisation

After substitution, the six axioms partition into four structural roles:

| Axioms | Substituted form | Role | Manifestation |
|--------|------------------|------|---------------|
| 1, 2, 3 | `(f # g) # h = f # (g # h)`, `f # lift id = f = lift id # f`, `lift (f . g) = lift f # lift g` | Free category | `Lift`, `Compose` constructors |
| 4 | `lower . lift = id` | Faithful embedding | `run (Lift f) = f` on interpretation |
| 5 | `p # (lift g # q) = lift g # (p # q)` | Centrality / braiding | Free from symmetry of tensor |
| 6 | `lower ((lift f # p) # q) = f . lower (q # p)` | Feedback / traced | `Loop` constructor, Mendler case |

Axioms 4 and 5 introduce no new constructors. Axiom 4 constrains interpretation;
axiom 5 holds automatically when the tensor is symmetric. Axiom 6 is the only
axiom that contributes structure: the `Loop` constructor for the feedback channel
and the Mendler case in `run` that mediates it via `trace` and `untrace`.

### the abstraction came last

This categorisation is retrospective. The actual path was:

1. Axiom 6 has a hidden channel implicit in how `run` ties the knot.
2. Costrength suggested naming the channel as an explicit tensor `t`.
3. `Loop :: arr (t a b) (t a c) -> Circuit arr t b c` was a guess.
4. The Mendler case `run (Compose (Loop f) g) = trace (f . untrace (run g))` was
   hacked in to make the types line up.
5. What fell out was recognised as a free traced monoidal category.

"Free traced monoidal category", the sliding axiom, and the `Trace` typeclass are
the retrospective description of what the hack turned out to be — not the design
principle.


---




## Why axioms 4, 5 & 6? 

The 2013 paper notes that without `<<` and its axioms, the system has a trivial model: `H a b = a -> b`, with `#` as function composition and `lift = id`. The axioms for `<<` are precisely what rule this out.

One clue is that the structure `lift f = f << lift f` is exactly the Y combinator unrolled one step:

```
Y f = f (Y f)
lift f = Trace f (lift f)
```

⟝ there is a complete switch here to hyperfunctions as the object, but we were narrating lift, not hyperfunctions.

Hyperfunctions are not all of lambda calculus — they represent the **fixed-point structure alone**: the part that requires domains or coinduction to make sense. This is why hyperfunctions don't have a set-theoretic interpretation. The axioms for `<<` enforce this feedback structure operationally.

⟝ There is no a or b or any diagonal.

The consequence: `run` on the diagonal (where `a = b`) extracts a fixed point via `run (lift f) = fix f` (Axiom 4). The axiom system is fundamentally about recursion and how to reify it in the type system.

---

## The Narrative Arc: From Coyoneda to Traced

Understanding circuits requires seeing the conceptual stack:

1. **Coyoneda** — Deferred application, free functor, `run . build = id`
2. **Free category** — Composition, Mendler inspection, the two-level type
3. **Traced category** — Feedback channel, fixed-point constructor, sliding axiom
4. **Laws** — Each level proven from the one below
5. **Adjunction** — Syntax (initial) meets semantics (final), unique interpretation functor
6. **Tensor choice** — `(,)` is holding hands (simultaneous); `Either` is taking turns (sequential)

Each level adds exactly one concept and names it honestly. The tower uses the same constructor names at multiple levels where they appear (e.g., `Coyoneda` in both Coyoneda and Free), making the structure transparent rather than opaque.

---

## A GADT for the Axioms

The operations suggest a GADT directly. Composition and feedback are the two constructors beyond the base category:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop    :: arr (t a b) (t a c) -> Circuit arr t b c
```

`Lift` embeds a base arrow. `Compose` is sequential composition. `Loop` opens a feedback channel: given a function that maps `(feedback, input)` to `(feedback, output)`, it closes the loop and produces a morphism `b -> c`.

The `Trace` typeclass provides the elimination:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `(->)` with `(,)`, `trace` is the arrow loop — `let (a,c) = f (a,b) in c` — and `untrace = fmap`. For `Either`, `trace` is `unright` — iterate until a `Right` is produced — and `untrace = fmap`.

The `Category` instance falls out immediately.

---

## The Naive Run

A first attempt at `run` follows the structure of the GADT:

```haskell
run (Lift f)      = f
run (Compose f g) = run f . run g
run (Loop k)      = trace k
```

This compiles and the Fibonacci example works:

```haskell
Loop (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
```

It is easy to believe this is correct. Axiom 7 states:

```
run ((f << p) # q) = f (run (q # p))
```

Substituting `f << p = Compose (Lift f) p`, the LHS reduces to `f . run p . run q` and the RHS to `f . run q . run p`. These are equal only if the two morphisms commute — not true in general. The naive run fails Axiom 7.

The Fibonacci example did not catch this because it has no `Compose` wrapping a `Loop` on the left. The failure only surfaces when something is composed after a feedback loop — when `run` needs to slide a morphism inside the trace.

---

## The Sliding Axiom

The nLab statement of sliding is:

```
tr^X((id_B ⊗ g) . f) = tr^Y(f . (id_A ⊗ g))
```

In plain terms: a morphism `g` composed on the output side of a trace can be moved to the input side. The trace is natural in its feedback object.

The naive run produces `trace f . run g` for `Compose (Loop f) g` — `run g` is applied once at entry. Sliding requires `run g` to participate on every pass through the loop. For `(,)` this distinction is invisible when the loop terminates in one step. For `Either`, where the loop iterates until a `Right` is produced, the two give different results.

---

## The Mendler Case

The fix is a single pattern match added to `run`:

```haskell
run :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
run (Lift f)             = f
run (Compose (Loop f) g) = trace (f . untrace (run g))
run (Compose f g)        = run f . run g
run (Loop k)             = trace k
```

When a `Loop` appears on the left of a `Compose`, `run g` is extracted and injected into the feedback channel via `untrace` before being handed to `trace`. For `(,)` this is `second (run g)`. For `Either` it is `fmap (run g)`.

The order of pattern matches is load-bearing. Without the `Compose (Loop f) g` case appearing before the general `Compose` case, it falls through and produces the naive — incorrect — behaviour.

This is the Mendler algebra step: inspecting one level of the syntax tree before recursing. Without it, `Loop` is observationally equivalent to `Lift (trace k)` — the feedback channel closes immediately, the loop structure is lost, and `Circuit` collapses to the free category with a fixed-point operator. This is the degenerate model the 2013 paper warns about.

---

## Hyperfunctions as the Final Encoding

`Circuit` is the initial encoding — a syntax tree whose `run` enforces the axioms. `Hyp` is the final encoding — a coinductive type whose structure *is* the axioms.

```haskell
newtype Hyp a b = Hyp { invoke :: Hyp b a -> b }
```

Composition:

```haskell
f . g = Hyp $ \h -> invoke f (g . h)
```

The backwards channel `h :: Hyp b a` is where the feedback lives. In `Circuit`, a `Loop` explicitly opens a feedback channel. In `Hyp`, every morphism already has one — the continuation argument `Hyp b a` is structurally present in every value. `Loop` does not go anywhere; it dissolves into the type.

The sliding axiom in `Hyp` is not enforced by inspection — it is inherent in `(.)`. The continuation `h` is threaded through `g . h` before `invoke f` sees it, on every unfolding. There is no degenerate model to fall into because the type itself encodes the feedback structure.

The map from syntax to semantics:

```haskell
unfold :: Circuit (->) (,) a b -> Hyp a b
unfold (Lift f)      = lift f
unfold (Compose f g) = unfold f . unfold g
unfold (Loop f)      = lift (trace f)
```

`unfold` is the unique traced functor from the initial object into `Hyp`, given by the universal property of `Circuit`. It does not need a Mendler case — the `Compose (Loop f) g` pattern reduces through the general `Compose` case:

```
unfold (Compose (Loop f) g)
  = unfold (Loop f) . unfold g    -- general Compose
  = lift (trace f) . unfold g     -- Loop case
```

No explicit `untrace`. Compare to `run`, which does apply `untrace`:

```
run (Compose (Loop f) g) = trace (f . untrace (run g))
```

The two agree through the sliding axiom of `Trace (->) t`:

```
trace (f . untrace g) = trace f . g
```

For `(,)`, `untrace = second`, and `trace (f . second g) = trace f . g` is the definition of sliding. For `Either`, `untrace = fmap` on `Right`, and the same equation holds. In both concrete cases `untrace = fmap` — the minimal action on the non-feedback channel — and it vanishes once pulled out of the `trace`.

Unfolding `lower . unfold` on the same term:

```
lower (unfold (Compose (Loop f) g))
  = lower (lift (trace f) . unfold g)
  = lower (lift (trace f)) . lower (unfold g)    -- lower is a functor
  = trace f . run g                              -- axiom 4 + induction
  = trace (f . untrace (run g))                  -- sliding axiom
  = run (Compose (Loop f) g)
```

The triangle `lower . unfold = run` holds because the sliding axiom closes it. The
`untrace` that `run` threads explicitly through `(->)` is absorbed into `Hyp`'s
composition `f . g = Hyp (\h -> invoke f (g . h))`, which threads the continuation
`h` through `g . h` on every unfolding — exactly the work `untrace = fmap` does, but
structural rather than operational.

The other direction is the forgetful map:

```haskell
degen :: Hyp a b -> Circuit (->) (,) a b
degen h = Lift (lower h)
```

`lower` observes the hyperfunction against a constant continuation, collapsing it to a plain function. All feedback structure is lost. `degen` is not an inverse to `unfold` — it is the observation that `Hyp` can only be seen from the outside.

The triangle closes: `lower . unfold = run`. Mapping `Circuit` into `Hyp` and then observing gives the same result as running `Circuit` directly.

---

|                    | `Circuit`                         | `Hyp`                        |
|--------------------|-----------------------------------|------------------------------|
| Encoding           | Initial (syntax)                  | Final (semantics)            |
| Sliding            | Enforced by Mendler inspection    | Inherent in `(.)`            |
| Feedback           | Explicit `Loop` constructor       | Structural in `Hyp` type     |
| Degenerate model   | Possible without Mendler case     | Not possible                 |
| Map to `(->)`      | `run`                             | `lower`                      |

The one-line change to `run` — adding the `Compose (Loop f) g` case — is the difference between `Circuit` being a free traced category and being the free category with a fixed-point operator.

---

## The Tensor is a Parameter

`Circuit arr t a b` abstracts over the tensor `t`. Both instances give valid traced categories and both support `unfold`:

| Tensor `t` | `trace`    | `untrace` | Operational character           |
|------------|------------|-----------|---------------------------------|
| `(,)`      | `unsecond` | `second`  | Lazy product knot; simultaneous |
| `Either`   | `unright`  | `fmap`    | While-loop; sequential handoff  |

`Hyp` is neutral to this choice — the feedback channel type does not appear in the `Hyp` newtype. `unfold` works for both tensors. The choice of tensor determines the operational behaviour of feedback, not the categorical structure.

**Costrong / `(,)`:** feedback and output exist in parallel. Both sides progress lock-step. Suitable for dataflow, zipping, true concurrency.

**Cochoice / `Either`:** sequential handoff — taking turns. Only one participant acts per step. Suitable for coroutines, schedulers, state machines.

The Kidney-Wu insight: the Producer/Consumer pattern decomposes simultaneous `(,)` into two sequential `Either` processes that communicate via message passing. This is why the hyperfunction type `a ↬ b` threads both directions through a single self-referential type — it unifies the two tensor perspectives through the duality of the continuation channel.

Every effects library that tries to do simultaneity on top of `Either` (merge, zipWith, concurrent pipelines, self-referential processes) is approximating `Costrong` with `Cochoice`. Each requires special combinators and breaks composition slightly. `Circuit` with `(,)` has one combinator: `Loop`. Everything else is derived.

---

## Operator Dictionary

| LKS 2013    | Kidney–Wu 2026 | `Circuit`            | Role                        |
|-------------|----------------|----------------------|-----------------------------|
| `f # g`     | `f ⊙ g`        | `Compose f g`        | Sequential composition      |
| `lift f`    | `rep f`        | `Lift f`             | Embed base arrow            |
| `f << h`    | `f ⊲ h`        | `Compose (Lift f) h` | Prepend function            |
| `run`       | `run`          | `run`                | Eliminate / tie knot        |
| _(implicit)_| _(implicit)_   | `Loop k`             | Feedback constructor        |
| `lower`     | `lower`        | `lower . unfold`     | Interpret to base arrow     |

---

## Axiom Correspondence

| LKS Axiom                                   | JSV / Hasegawa counterpart           | `Circuit` location         | Notes                                 |
|---------------------------------------------|--------------------------------------|----------------------------|---------------------------------------|
| 1: `(f # g) # h = f # (g # h)`              | Monoidal associativity               | `Category` instance        | Pre-condition                         |
| 2: `f # self = f = self # f`                | Vanishing I                          | `Lift id`                  | `self = lift id` is identity          |
| 3: `lift (f . g) = lift f # lift g`         | Functor law                          | `Lift`                     | Strict monoidal functor               |
| 4: `run (lift f) = fix f`                   | Yanking (cartesian specialisation)   | `run (Loop ...)`           | Trace induces `fix` in cartesian case |
| 5: `(f << p) # (g << q) = (f.g) << (p # q)` | Superposing                          | `Compose` + `Lift`         | `<<` encodes feedback channel         |
| 6: `lift f = f << lift f`                   | Vanishing II / coinductive unfolding | `Lift` under `Compose`     | Loop unrolling                        |
| 7: `run ((f << p) # q) = f (run (q # p))`   | **Sliding**                          | `run (Compose (Loop f) g)` | Demands `Loop`                        |

LKS Axiom 7 is the sliding/naturality axiom. Without `Loop`, a free category built from `Lift` and `Compose` alone cannot satisfy it.

---

## Hasegawa's cartesian specialisation

In a cartesian traced category, Hasegawa's Theorem 3.1 establishes that the trace is equivalent to a fixed-point operator satisfying the Conway axioms. This is why `run (lift f) = fix f` (LKS Axiom 4) is not an arbitrary choice — in the cartesian setting, any trace necessarily induces `fix`. The connection is a theorem, not a definition.

Hasegawa also separates cyclic sharing (the trace) from fixed-point combinators: they agree extensionally but differ operationally. The fixed-point combinator can cause resource duplication in sharing-based implementations; the trace does not. This maps onto the `Costrong` vs `Cochoice` distinction: not just a design preference but a semantic difference with operational consequences.

---

## The Kan Extension

The Icelandjack observation: `Hyp a b = Fix (Ran (Const a) (Const b))`.

Computing the Ran via the end formula:

```
Ran (Const a) (Const b) x  =  ∫_c Hom(a, x) → b
                             =  (a -> x) -> b
```

The end over `c` vanishes because neither constant functor depends on `c`. This is a continuation — give a function from `a` to the answer type `x`, and receive a `b`.

`Fix` ties the knot on `x`, replacing it with the whole type flipped:

```
Fix (Ran (Const a) (Const b))  =  (Fix (Ran (Const b) (Const a)) -> b)
                                =  (Hyp b a -> b)
                                =  Hyp a b
```

The fixpoint is the self-referential duality: to produce a `b`, invoke the dual `Hyp b a`. The Ran gives the continuation structure; the Fix gives the knot.

`Circuit a b ~ Ran (Const a) (Const b)` (before the Fix). The embedding `Lift : (a → b) → Circuit a b` is the Kan counit, and `run` is what recovers `(a → b)` from the Ran structure — the counit of the adjunction. The Mendler case enforces naturality of this counit with respect to composition; without it, the universal property is violated and `Loop` collapses.

The universal property stated categorically: for any traced monoidal category `C` and functor `F : arr -> C`, there is a unique traced functor `Circuit arr t -> C` extending `F`. When `C = Hyp`, that unique functor is `unfold`. `Hyp` is the codensity/Yoneda representation of `Circuit` with feedback baked into the type rather than sitting as an explicit constructor.

The triangle `lower . unfold = run` is the unit-counit identity: `run` eliminates the initial encoding, `lower` observes the final encoding, and they agree because they are the same universal map viewed from opposite sides.

---

## Reflection without Remorse: The Traced Category Extension

**Reference:** van der Ploeg & Kiselyov, Haskell 2014

The paper establishes a hierarchy for solving the build-and-observe performance problem:

| Structure | Naive       | CPS / Codensity | Explicit sequence     |
|-----------|-------------|-----------------|----------------------|
| Monoid    | list        | difference list | queue                |
| Monad     | free monad  | codensity monad | type-aligned queue   |
| Category  | `Cat`       | `Queue` (Ran)   | type-aligned queue   |

The paper stops at categories. The natural next row is:

| Traced category | `TracedA` | `HypA` (Fix . Ran) | type-aligned queue + Fix |

### The direct mappings

**Left-nested composition.** Left-nested `>>=` in the paper produces O(n²) performance. Left-nested `Compose` in `TracedA` produces the same problem — and worse, without the Mendler case, `Loop` gets buried under the left-nesting and collapses to the degenerate model.

**The hidden sequence.** The paper's title refers to the implicit sequence of monadic binds, made explicit by a type-aligned queue. In `TracedA`, the hidden structure is the feedback channel inside `Loop`. Both are made explicit by the respective constructions: the queue in the paper, the `Loop` constructor here.

**`PMonad` and `Trace`.** The paper introduces `PMonad`, an alternative to `Monad` where bind takes an explicit type-aligned sequence as its right argument rather than a single continuation:

```haskell
class PMonad m where
  return' :: a -> m a
  (>>^=) :: m a -> MCExp m a b -> m b
```

This is structurally the same move as the `Trace` class: instead of hiding the feedback channel inside the monad, make it an explicit typed argument:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- observe the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into the channel
```

`untrace` is the analogue of `expr = tsingleton` in the paper — converting a single morphism into the explicit sequence representation. `trace` is the analogue of `val` — observing the head of the sequence and reducing.

**`viewl` is the Mendler case.** The paper's solution requires `viewl` on the type-aligned queue to inspect the head of the sequence before recursing. In `run`, the Mendler case does exactly this:

```haskell
run (Compose (Loop f) g) = trace (f . untrace (run g))
```

When a `Loop` appears at the head of a composition, inspect it before recursing into `g`. Without this case, `run` falls through to the general `Compose` rule, buries the `Loop`, and produces the degenerate model — the traced category collapses to the free category with a fixed-point operator. This is the remorse: `Loop` becomes observationally equivalent to `Lift (trace k)`.

```
Cat  +  viewl  =  Queue         -- reflection without remorse for categories
Circuit  +  Mendler  =  Hyp     -- reflection without remorse for traced categories
```

### The full hierarchy

| Structure       | Naive     | Efficient (Ran / Fix.Ran) | Inspection mechanism     |
|-----------------|-----------|---------------------------|--------------------------|
| Monoid          | list      | difference list            | head/tail                |
| Monad           | free monad| codensity monad            | `viewl` on TCQueue       |
| Category        | `Cat`     | `Queue`                    | `viewl` on type-aligned queue |
| Traced category | `Circuit` | `Hyp`                      | Mendler case in `run`    |

---

## Costrength: The Categorical Backing for Trace

**Reference:** Balan & Pantelimon, "The Hidden Strength of Costrong Functors" (2025)

The `Trace` typeclass bundles two directions of a monoidal action:

```haskell
class Trace arr t where
  untrace :: arr b c -> arr (t a b) (t a c)   -- STRONG:   push action inside
  trace   :: arr (t a b) (t a c) -> arr b c   -- COSTRONG: pull action out
```

This is the formal definition of an M-costrong functor. The paper's costrength natural transformation `cst : F(M . X) -> M . F(X)` is exactly `trace`. The strength `st : M . F(X) -> F(M . X)` is exactly `untrace`.

### Theorem 3.2: Costrong = Copointed on cartesian categories

On a cartesian category, costrong endofunctors are in bijection with copointed endofunctors — those equipped with a natural transformation `ε : F -> id`. The costrength `cst` corresponds to `ε` via:

```
ε : F(M) -> M    given by    F(M) ≅ F(M x 1) -> M x F(1) -> M
```

For our `trace`: the copoint `ε` is exactly the operation that extracts a plain arrow from a traced one. `trace` is the copoint of the traced structure.

### Proposition A.4: Free constructions inherit costrength

If the generating functor `F` is M-costrong, so is the free monad on `F`. `Circuit` is the free traced category over `arr`. If `arr` supports `Trace` (is costrong with respect to `t`), then `Circuit` inherits it. This is the categorical justification for why the `Trace` instance on `Circuit` is well-defined and not just ad hoc.

### Section 4.2: Costrength and streams

A costrong functor `F` lifts to stream coalgebras: `cst : F(M x X) -> M x F(X)` keeps the output channel observable through the context `F`. For `Either` tensor, this is exactly the while-loop trace — `Right` (the output) remains extractable from within `F` on every iteration. The stream lifting result formally backs the `Trace (->) Either` instance as a valid costrength.

### The optics connection

Section 4.1: an M-costrong functor paired with an M-strong functor gives an optics transformer. Our `(trace, untrace)` pair is this exactly — `trace` costrong, `untrace` strong. Together they define the traced optic structure, and this is the formal backing for the profunctor instances (`Costrong`, `Strong`, `Cochoice`, `Choice`) on `Circuit`.

The `Trace` typeclass is not an ad hoc design — it is the interface of a costrong/strong adjoint pair, formalised independently in the optics literature.

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

`Queue f a b` is `Ran (Cat f) (Cat f)` — the free category represented via its universal property rather than as explicit lists. Same category, O(1) amortised composition instead of O(n).

Adding `Loop` (the trace) to the free category requires a fixpoint, because feedback loops back on itself. The same Cayley move applied to the free *traced* category gives `Hyp`:

```haskell
Hyp a b  =  Hyp b a -> b    -- Fix (Ran (Const a) (Const b))
```

The hierarchy:

| Level              | Initial (syntax)  | Final (semantics) | What the step adds |
|--------------------|-------------------|-------------------|--------------------|
| Free category      | `Cat` / `LiftCompose` | `Queue`       | Yoneda / Ran       |
| Free traced category | `Circuit`       | `Hyp`             | Fix (feedback)     |

`Queue` is `Ran` of the free category along itself. `Hyp` is `Fix(Ran(Const a)(Const b))` — the `Fix` is exactly what `Loop` contributes. Feedback requires a fixpoint; the free category does not.

The universal property stated categorically: for any traced monoidal category `C` and functor `F : arr -> C`, there is a unique traced functor `Circuit arr t -> C` extending `F`. When `C = Hyp`, that unique functor is `unfold`. `Hyp` is the codensity/Yoneda representation of `Circuit` with the feedback baked into the type rather than sitting as an explicit constructor.

The triangle `lower . unfold = run` is the unit-counit identity of this adjunction: `run` eliminates the initial encoding, `lower` observes the final encoding, and they agree because they are the same universal map viewed from opposite sides.

---

## Open Questions

- Prove that the Mendler case in `run` is exactly the counit naturality of `Ran (Const a) (Const b)`, formalised.
- Establish the precise isomorphism `Circuit a b ~ Ran (Const a) (Const b)` as a theorem, not a diagram observation.
- Establish that `Loop` is the unique reifier of the hidden channel in axiom 6 — i.e. `unfold` is the unique traced functor `Circuit -> Hyp`, not merely a traced functor. The freeness of `Circuit` as a traced monoidal category depends on this.
- Clarify whether `Fix (Circuit (->) t)` is well-typed at all, and if so, whether `Hyp a b ~ Fix (Circuit (->) t a b)` is an iso or strict inequality. `unfold` exists but `degen` is lossy, so the two encodings are not isomorphic on the nose — the precise adjunction needs to be stated.
- The Geometry of Interaction connection (Int(C) completion, `callCC`, shift/reset) is a conjecture not yet developed.
- The graded structure counting `Loop` depth and its implications for Okasaki queue amortisation are noted but not formalised.
- Map concrete Kidney–Wu examples (breadth-first search via Hofmann, concurrency scheduler) onto `Circuit`/`Hyp`.

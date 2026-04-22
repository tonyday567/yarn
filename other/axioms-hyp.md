# Hyperfunction Axioms

Semantics based on Kidney|Wu 2026

Axioms from LKS, Launchbury 2013

---

## semantics

### invoke

```haskell
   -- | A hyperfunction invokes its own dual to produce a value.
   newtype Hyp a b = Hyp { invoke :: Hyp b a → b }
```

A hyperfunction `a ↬ b` is defined as a function that invokes its own dual (`b ↬ a`) to produce a value.

The structure is self-referential through duality. You can't define `a ↬ b` without reference to `b ↬ a`, and vice versa.

```haskell
invoke' :: (a ↬ b) → (b ↬ a) → b
invoke' f g = run (f # g)
```

**Proof that `invoke = invoke'`:** By the bridge law (9), `ι f g = run (f # g)`. Since
`invoke f g = ι f g` by definition and `invoke' f g = run (f # g)`, the two are
definitionally equal. ✓

### lift

```haskell
lift :: (a → b) → (a ↬ b)
lift f = f << lift f
```

Lifting a function into Hyp is defined recursively. It constructs hyperfunctions by
repeated application of `<<` under lazy evaluation.

### push (<<)

```haskell
(<<) :: (a → b) → (a ↬ b) → (a ↬ b)
f << h = Hyp (\k -> f (invoke k h))
```

Inductively:

```
ι (f << h) k = f (ι k h)     (6)
```

### zip (#)

```haskell
(#) :: (b ↬ c) → (a ↬ b) → (a ↬ c)
f # g = Hyp $ \h -> ι f (g # h)
```

```
ι (f # g) h = ι f (g # h)     (7)
```

The inductive form of zip surfaces its right-reassociation action under invoke.

### run ⟲

**Kidney–Wu definition (self-referential):**
```haskell
run :: a ↬ a → a
run h = ι h (Hyp run)     (8)
```

`run` ties the knot: it invokes `h` with `Hyp run` — itself repackaged as a
hyperfunction — creating the recursive closure.

**LKS definition (grounded in identity):**
```haskell
run :: a ↬ a → a
run h = invoke h (rep id)
```

**Proof that both definitions are equivalent:**

We need `ι h (Hyp run) = invoke h (rep id)` for all `h :: a ↬ a`.

By the bridge law (9), `invoke h (rep id) = run (h # rep id)`. By Axiom 2 (right
identity), `h # rep id = h`. So `invoke h (rep id) = run h = ι h (Hyp run)` by (8). ✓

---

### helpers

```haskell
lower :: (a ↬ b) → (a → b)
lower q x = invoke q (base x)

base :: a -> b ↬ a
base x = lift (const x)

fix :: (a → a) → a
fix f = f (fix f)
```

---

## LKS Axioms in Modern Notation (Launchbury, Krstic & Sauerwein → Kidney–Wu)

### Axiom 1 — Associativity of #
```
(f # g) # h = f # (g # h)
```

**Proof:** By (7), for any `k`:
```
ι ((f # g) # h) k
  = ι (f # g) (h # k)         -- by (7)
  = ι f (g # (h # k))         -- by (7)
  = ι f ((g # h) # k)         -- by Axiom 1 applied coinductively to tail
  = ι (f # (g # h)) k         -- by (7)
```
✓

---

⟝ switch rep to lift

### Axiom 2 — Identity of #
```
f # rep id = f = rep id # f
```

**Proof (right identity):** In the L model, `rep id = id :<<: rep id`, so:
```
(f << p) # rep id
  = (f << p) # (id << rep id)    -- by def of rep
  = (f . id) << (p # rep id)     -- by Axiom 5
  = f << (p # rep id)            -- f . id = f
```
By coinduction, `p # rep id = p`, so `(f << p) # rep id = f << p`. ✓

**Proof (left identity):** Similarly:
```
rep id # (g << q)
  = (id << rep id) # (g << q)    -- by def of rep
  = (id . g) << (rep id # q)     -- by Axiom 5
  = g << (rep id # q)            -- id . g = g
```
By coinduction, `rep id # q = q`. ✓

---

### Axiom 3 — rep is a Functor
```
rep (f . g) = rep f # rep g
```

**Proof:**
```
rep f # rep g
  = (f << rep f) # (g << rep g)    -- by def of rep
  = (f . g) << (rep f # rep g)     -- by Axiom 5
  = rep (f . g)                    -- by def of rep, coinductively
```
✓

---

### Axiom 4 — run is Fixed-Point
```
run (lift f) = fix f
```

**First, the push elimination rule:**
```
run (f << fs) = f (run fs)
```

**Proof:** From (6) and (8):
```
run (f << fs)
  = ι (f << fs) (Hyp run)      -- by (8)
  = f (ι (Hyp run) fs)         -- by (6)
  = f (run fs)                 -- by (8): ι (Hyp run) h = run h
```

**Proof of the axiom.** Unfolding `lift f = f << lift f` and applying the rule:
```
run (lift f)
  = run (f << lift f)     -- by def of lift
  = f (run (lift f))      -- by push elimination
```

So `run (lift f)` satisfies `x = f x`. By definition of `fix`, `run (lift f) = fix f`. ✓

---

### Axiom 5 — Prefix Composition
```
(f << p) # (g << q) = (f . g) << (p # q)
```

**Proof:** By (6) and (7), for any `k`:
```
ι ((f << p) # (g << q)) k
  = ι (f << p) ((g << q) # k)       -- by (7)
  = f (ι ((g << q) # k) p)          -- by (6)
  = f (ι (g << q) (k # p))          -- by (7)
  = f (g (ι (k # p) q))             -- by (6)
  = f (g (ι k (q # p)))             -- by (7)
  = (f . g) (ι k (q # p))           -- function composition
  = ι ((f . g) << (p # q)) k        -- by (6)
```
✓

---

### Axiom 6 — Run with Prefix
```
run ((f << p) # q) = f (run (q # p))
```

**Proof attempt in the continuation model.** Expanding via (6), (7), (8):
```
run ((f << p) # q)
  = ι ((f << p) # q) (Hyp run)      -- by (8)
  = ι (f << p) (q # Hyp run)        -- by (7)
  = f (ι (q # Hyp run) p)           -- by (6)
  = f (ι q (Hyp run # p))           -- by (7)
```

We need this to equal `f (run (q # p)) = f (ι q (p # Hyp run))` by (8) and (7). The
proof requires `Hyp run # p = p # Hyp run`. Testing this with `p = h << ps`:

```
ι (Hyp run # p) k = ι (Hyp run) (p # k) = run (p # k) = run ((h << ps) # k)
ι (p # Hyp run) k = ι p (Hyp run # k)   = h (ι (Hyp run # k) ps) = h (run (k # ps))
```

Equating these gives `run ((h << ps) # k) = h (run (k # ps))`, which is exactly
Axiom 6 again. **The continuation-model proof is circular.** Axiom 6 cannot be
derived from (6)–(8) without presupposing it. LKS correctly lists it as a primitive.

**Proof in the L model (coinductive).** In L, `#` is pairwise composition on streams
and `run (f :<<: fs) = f (run fs)`. Write `p = h :<<: ps` and `q = g :<<: qs`:

```
LHS: run ((f << p) # q)
  = run ((f . g) :<<: (p # qs))       -- by def of # in L (Axiom 5)
  = (f . g) (run (p # qs))            -- by def of run in L
  = (f . g) (h (run (qs # ps)))       -- by Axiom 6 coinductively on (p # qs)

RHS: f (run (q # p))
  = f (run ((g . h) :<<: (qs # ps)))  -- by def of # in L
  = f ((g . h) (run (qs # ps)))       -- by def of run in L
  = (f . g . h) (run (qs # ps))
```

LHS = RHS. The coinduction is well-founded: each step consumes one stream constructor
and the streams are productive. ✓

---

## lift ⊣ lower: The Adjunction

`lift` and `lower` form an adjunction between ordinary functions and hyperfunctions.

**Unit — lower ∘ lift = id:**
```
lower (lift f) = f
```

**Proof:**
```
lower (lift f) x
  = invoke (lift f) (base x)                          -- by def of lower
  = run (lift f # base x)                             -- by bridge law (9)
  = run ((f << lift f) # lift (const x))              -- by def of lift, base
  = run ((f . const x) << (lift f # lift (const x)))  -- by Axiom 5
  = (f . const x) (run (lift f # lift (const x)))     -- by push elimination
  = f x                                               -- f . const x = \_ -> f x
```
✓

**Diagonal specialisation — run = fix ∘ lower (L model):**

In the L model `lift . lower = id` (the counit: every hyperfunction is a stream of
functions, and `lift . lower` reconstructs it exactly). Given this:

```
run . lift = fix                -- Axiom 4
run . lift . lower = fix . lower
run . (lift . lower) = fix . lower
run . id = fix . lower          -- by counit: lift . lower = id
run = fix . lower
```

**Note on the counit.** The unit `lower . lift = id` is proved above from the axioms.
The counit `lift . lower = id` is strictly stronger: it says every hyperfunction is
determined by its action on constant inputs. This holds in the L model by construction
but is not derivable from the axioms in general. `run = fix . lower` is therefore a
theorem about the L model specifically, not the axiomatic theory.

---

## Restated Axioms: fix and run factored out

With `run = fix . lower` in the L model, Axioms 4 and 6 restate purely in terms of
`lower`.

**Axiom 4 restated:**
```
lower (lift f) = f
```

`run . lift = fix` is then a consequence: `fix . lower . lift = fix . id = fix`.

**Axiom 6 restated** — lower distributes over feedback:

Substituting `run = fix . lower` into Axiom 6 and cancelling `fix` (which appears
uniformly on both sides):
```
run ((f << p) # q) = f (run (q # p))
    ↓ substitute
fix (lower ((f << p) # q)) = f (fix (lower (q # p)))
    ↓ cancel fix
lower ((f << p) # q) = f . lower (q # p)
```

`fix` becomes an operational detail; the algebraic content lives in `lower`.

---

## GADTs: The Free Traced Category

The restated axioms determine a GADT whose `lower` map is the unique interpretation
functor. We build it in three steps.

### Step 1 — Push and Compose

The two operations on hyperfunctions are `<<` (prepend a function) and `#` (compose
two hyperfunctions). Writing them directly as constructors:

```haskell
data L a b where
  Push    :: (a -> b) -> L a b -> L a b
  Compose :: L b c -> L a b -> L a c

lower (Push f g)    = f . lower g
lower (Compose f g) = lower f . lower g

instance Category L where
  id  = Push id id
  (.) = Compose
```

### Step 2 — Factor Push into Lift + Compose

`lower` applies the same treatment to its second argument in both cases: recurse and
compose on the left. The redundancy dissolves when `Push f g` is read as
`Compose (Lift f) g`:

```haskell
data L a b where
  Lift    :: (a -> b) -> L a b
  Compose :: L b c -> L a b -> L a c

lower (Lift f)      = f
lower (Compose f g) = lower f . lower g

instance Category L where
  id  = Lift id
  (.) = Compose
```

This is the **free category** on `(->)`. The original operators translate as:

```haskell
f << h  =  Compose (Lift f) h
f #  g  =  Compose f g              -- # is just Compose
lift f  =  fix (Compose (Lift f))   -- recursive fixed point
```

### Step 3 — Axiom 6 demands a Trace constructor

The restated Axiom 6 is:
```
lower ((f << p) # q) = f . lower (q # p)
```

Expanding with Step 2 constructors (`f << p = Compose (Lift f) p`, `# = Compose`):

```
lower (Compose (Compose (Lift f) p) q)
  = lower (Compose (Lift f) p) . lower q   -- by lower of Compose
  = (f . lower p) . lower q
  = f . lower p . lower q

f . lower (Compose q p)
  = f . lower q . lower p
```

The axiom requires:

```
f . lower p . lower q  =  f . lower q . lower p
```

Cancelling `f`: `lower p . lower q = lower q . lower p`.

Since `lower` interprets as plain function composition, this demands that arbitrary
`lower p` and `lower q` commute — something no term built from `Lift` and `Compose`
can guarantee. Axiom 6 encodes a **feedback** relationship invisible to a free
category.

### The feedback constructor

When `p` and `q` share a hidden state channel `s` that cycles between them, the swap
is valid: the apparent reordering is a repackaging of the same cyclic computation.
Concretely, `f :: (s, a) -> (s, b)` with `s` existential allows `lower` to tie the
knot:

```haskell
unfirst :: ((s, a) -> (s, b)) -> (a -> b)
unfirst f a = b
  where (s, b) = f (s, a)    -- lazy knot-tying over the hidden channel s
```

This gives the third constructor:

```haskell
data L a b where
  Lift    :: (a -> b) -> L a b
  Compose :: L b c -> L a b -> L a c
  Trace   :: (forall s. L (s, a) (s, b)) -> L a b

lower (Lift f)      = f
lower (Compose f g) = lower f . lower g
lower (Trace f)     = unfirst (lower f)
```

**Why `Trace` satisfies Axiom 6.** The restated axiom needs
`lower p . lower q = lower q . lower p` when `p = Trace g`. Substituting:

```
lower (Trace g) . lower q
  = unfirst (lower g) . lower q
```

The knot inside `unfirst` routes the output of `lower g` back through the existential
`s`. Because `s` does not appear in the external types `a` or `b`, sliding `lower q`
past the feedback loop is valid — this is exactly the **sliding axiom** of traced
monoidal categories:

```
trace (f . second g) = trace (second g . f)
```

In our cartesian setting with `second g = id ⊗ lower q`:

```
unfirst (lower g . second (lower q)) = unfirst (second (lower q) . lower g)
```

which gives `unfirst (lower g) . lower q = lower q . unfirst (lower g)`, i.e.
`lower (Trace g) . lower q = lower q . lower (Trace g)`. ✓

### L as the free traced category

The three constructors correspond exactly to the three generators of a traced
symmetric monoidal category:

| Constructor | Role                     | Categorical name |
|-------------|--------------------------|------------------|
| `Lift`      | Inject a base arrow      | Embedding        |
| `Compose`   | Sequential composition   | Composition      |
| `Trace`     | Feedback / knot-tying    | Trace            |

`lower` is the **unique traced functor** `L -> (->)`, interpreting each constructor
in the category of functions. `Trace` maps to `unfirst`, which is `fix`-powered
knot-tying — hence `run = fix . lower` on the diagonal. The two are the same
operation: `run` ties the knot lazily across the whole stream; `unfirst` ties it
locally across the hidden channel.

```haskell
instance Category L where
  id  = Lift id
  (.) = Compose

instance TracedMonoidal (,) L where
  trace = Trace

lower :: L a b -> (a -> b)
lower (Lift f)      = f
lower (Compose f g) = lower f . lower g
lower (Trace f)     = unfirst (lower f)
```

### Open question

The `Trace` constructor makes the feedback channel `s` explicit in the type. The
original Axiom 6 — `run ((f << p) # q) = f (run (q # p))` — leaves it implicit: `p`
and `q` are ordinary `a ↬ a` terms, and the feedback lives in the way `run` ties the
knot across both. The remaining gap is making the translation precise: given a
concrete pair `(p, q)` satisfying Axiom 6, what is the existential `s`, and how does
the `Trace` term that encodes them factor through `lower`?



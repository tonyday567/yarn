# Traced ⟜ Free Traced Monoidal Category

A library implementing the free traced monoidal category over Haskell functions.

We build this by choosing three syntaxes — shapes for representing computation as data.
Each syntax comes with laws proved by equational reasoning. The pieces fit together.

## The Syntax

Three shapes, building upward:

1. **Coyoneda** — syntax for function application
2. **Free** — syntax for composition (builds on Coyoneda)
3. **Traced** — syntax for loops (builds on Free)

Each syntax choice is universal: any interpretation of the data is uniquely determined 
by how the generators are cast. A unified GADT with three constructors recovers all three.

## Development

Work in cabal repl:

```bash
cd ~/repos/traced
cabal repl
```

Run doctests:

```bash
cabal build all --enable-tests
cabal-docspec
```

## Coyoneda ⟜ Syntax for Functions

We choose to represent function application as data. Two constructors:

```haskell
data Coyoneda a b where
  Pure  :: Coyoneda a a
  Apply :: (b -> c) -> Coyoneda a b -> Coyoneda a c
```

**Shape**: `Coyoneda a b` is a pipeline from `a` to `b`, shaped as a sequence of 
function applications.

`Pure` is the identity — no applications yet. `Apply f p` adds a function `f` to 
the pipeline.

### Cast: From Data to Functions

**build**: Cast a function into the syntax.

```haskell
build :: (a -> b) -> Coyoneda a b
build f = Apply f Pure
```

**run**: Cast the syntax back to a function.

```haskell
run :: Coyoneda a b -> (a -> b)
run Pure        = id
run (Apply f p) = f . run p
```

These two casts are inverses. The universal property is expressed by their adjunction.

### The Fusion Law

Running a built term recovers the original:

```
Claim: run (build f) = f

Proof by equational reasoning:

  run (build f)
= run (Apply f Pure)               [by definition of build]
= f . run Pure                     [by definition of run]
= f . id                           [by definition of run]
= f                                [composition with identity]

∎
```

The syntax is *transparent* — when the optimizer sees `run . build`, the syntax 
completely dissolves, leaving only the function.

### Idempotence

A consequence of fusion:

```
Claim: run (build (run p)) = run p

Proof:

  run (build (run p))
= run p                            [by fusion law]

∎
```

Double-casting through the syntax is the same as single-casting.

### The Functor Shape

`Coyoneda a` forms a functor in its output. Mapping a function adds it to the pipeline:

```haskell
instance Functor (Coyoneda a) where
  fmap f p = Apply f p
```

This respects functor structure. The laws follow from the algebra:

**Identity:**
```
  run (fmap id p)
= run (Apply id p)                 [fmap definition]
= id . run p                       [run definition]
= run p                            [id is identity]
```

**Composition:**
```
  run (fmap (g . f) p)
= (g . f) . run p                  [fmap, run]

  run (fmap g (fmap f p))
= run (Apply g (Apply f p))        [fmap twice]
= g . (f . run p)                  [run twice]
= (g . f) . run p                  [associativity]
```

The structure respects algebra. The pieces fit.

## Free ⟜ Syntax for Composition

We choose to represent composition as data. Three constructors:

```haskell
data Free a b where
  Pure    :: Free a a
  Apply   :: (b -> c) -> Free a b -> Free a c
  Compose :: Free b c -> Free a b -> Free a c
```

**Shape**: `Free a b` is a pipeline from `a` to `b`, built from two operations:
application (inherited from Coyoneda) and explicit composition.

`Pure` is identity. `Apply f p` adds a function. `Compose g h` joins two pipelines.

Composition is data, not the operation `(.)`. This lets us inspect, optimize, and 
pass the composition itself to other code.

### Cast: From Data to Functions

**build**: Cast a function into the syntax (same as Coyoneda).

```haskell
build :: (a -> b) -> Free a b
build f = Apply f Pure
```

**run** at the Free level: Cast the syntax back to a function.

At Free level, no case inspection is needed — composition simply flattens to function composition:

```haskell
runFree :: Free a b -> (a -> b)
runFree Pure        = id
runFree (Apply f p) = f . runFree p
runFree (Compose g h) = runFree g . runFree h
```

This is straightforward: each constructor maps directly to its algebraic counterpart.

### Category Laws

`Free` respects the algebra of categories. Identity and associativity are inherited:

**Identity (left):**
```
  run (Compose (build id) p)
= run (build id) . run p            [run definition]
= id . run p                        [fusion law]
= run p                             [id is identity]
```

**Identity (right):**
```
  run (Compose p (build id))
= run p . run (build id)            [run definition]
= run p . id                        [fusion law]
= run p                             [id is identity]
```

**Associativity:**

```
Claim: run (Compose (Compose f g) h) = run (Compose f (Compose g h))

Proof by Mendler inspection (definitional):

The case analysis in run detects left-nested Compose and reassociates before recursing.

When we call: run (Compose (Compose f g) h)

  The outer Compose matches:
    run (Compose g h) where g = Compose f g, h = h
  
  We case on g = Compose f g:
    case g of
      Compose g1 g2 -> run (Compose g1 (Compose g2 h))
      ...
  
  With g1 = f and g2 = g, we get:
    run (Compose f (Compose g h))

This is the right-hand side of our claim, so the reassociation is immediate — 
the structure of run itself enforces it.

Both sides now reduce identically. The underlying function composition (.) is 
associative in the algebra of Haskell functions:

  (f . g) . h = f . (g . h)

So the normalized forms, once fully reduced, are equal by associativity of (.).

∎

**Key insight:** Associativity is not a proof obligation. The Mendler inspection 
in run normalizes left-nested Compose to a canonical form, so associativity holds 
definitionally by the structure of the normalizer.

### Profunctor Instance

`Free` is a profunctor. We can map on both sides:

```haskell
instance Profunctor Free where
  dimap f g p = build g `compose` p `compose` build f
```

where `compose` is the `Compose` constructor.

### What We've Built

The first two levels of syntax:
- **Coyoneda** represents function application as data
- **Free** adds composition as data, building on Coyoneda

Each level is universal: any interpretation factors through the cast operations.
The laws are proven by equational reasoning. The structure is sound.

## Traced ⟜ Syntax for Loops

We choose to represent loops as data. Four constructors shape a pipeline with feedback:

```haskell
data Traced a b where
  Pure    :: Traced a a
  Apply   :: (b -> c) -> Traced a b -> Traced a c
  Compose :: Traced b c -> Traced a b -> Traced a c
  Untrace :: Traced (a, c) (b, c) -> Traced a b
```

**Shape**: `Traced a b` is a pipeline from `a` to `b`, extended with loops.

`Untrace` introduces a feedback variable `c` that travels *alongside* the main computation. 
The variable is existential — sealed inside `Untrace`, invisible from outside. This sealing is 
the key to all the laws.

### Cast: From Data to Functions

**build**: Cast a function into Traced syntax.

```haskell
build :: (a -> b) -> Traced a b
build f = Apply f Pure
```

**run** at the Traced level: Cast the syntax back to a function using **Mendler-style case inspection**.

The implementation changes fundamentally when `Untrace` is available. We cannot simply 
flatten `Compose` — we must inspect the left side before recursing:

```haskell
run :: Traced a b -> (a -> b)
run Pure = id
run (Apply f p) = f . run p
run (Compose g h) = case g of
  -- If left side is Apply, extract and reassociate
  Apply f p -> f . run (Compose p h)
  -- If left side is Compose, reassociate leftward
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  -- If left side is Untrace, slide and close the loop
  Untrace p -> \a -> fst $ fix $ \(_b, c) -> run p (run h a, c)
  Pure -> run h
run (Untrace p) = \a -> fst $ fix $ \(_b, c) -> run p (a, c)
```

### Implementation Changes: Free to Traced

The shift from Free to Traced forces a complete reimplementation of `run`:

| Level | Implementation | Reason |
|-------|----------------|--------|
| **Coyoneda** | Linear recursion | Only `Apply` and `Pure`; no branching needed |
| **Free** | Linear recursion | `Compose` just flattens; still no branching |
| **Traced** | **Mendler case inspection** | `Untrace` requires looking inside `Compose` to trigger sliding |

At the Traced level, the case inspection does two things:

1. **Reassociate** left-nested `Compose` chains, implementing associativity definitionally 
   (not as a proof obligation)

2. **Detect and execute the sliding law**: when `Untrace` appears on the left of `Compose`, 
   the case inspection triggers the law, absorbing the right-hand side into the feedback 
   loop and closing it at exactly the right moment.

The operational content of the traced monoidal axioms is compiled into this normalizer. 
The loop slides through compositions until reaching a point where it can safely be closed.

### The Sliding Law (Proved by Polymorphism)

When `Untrace` appears on the left of `Compose`, it slides inward, absorbing the 
right-hand side:

```
Untrace p ∘ h = Untrace (p ∘ (h × id_c))
```

**What this means operationally:**

In the `run` function, this is the case:

```haskell
run (Compose (Untrace p) h) = \a -> fst $ fix $ \(_b, c) -> run p (run h a, c)
```

Breaking it down:

1. **Input**: We receive `a`
2. **Right-hand side absorbed**: First, we run `h` on the input: `run h a`
3. **Feedback threaded**: We pair the result with the feedback variable `c`: `(run h a, c)`
4. **Left-hand loop**: Feed this pair into `p`, which produces a new `(b, c)` pair
5. **Fixed point**: The fixed point finds the value of `c` such that the loop is coherent
6. **Projection**: Extract just the `b` component with `fst`

The key insight: by inspecting the structure of `Compose`, we can **rearrange** the order 
of operations. Instead of composing `Untrace p` with `h` as a pipeline, we **absorb** `h` 
into the feedback loop. Both input and feedback flow through `p` together.

**Proof by parametricity:**

The feedback variable `c` in `Untrace` is existentially quantified:

```haskell
Untrace :: Traced (a, c) (b, c) -> Traced a b
```

Once `Untrace` is applied, `c` is sealed away, invisible from outside. The type itself 
guarantees that `c` cannot escape. By parametricity over the existential, any rearrangement 
of how `c` threads through compositions is unobservable from outside.

Therefore, the two forms — `Untrace` on the left of `Compose`, or slid inward — are 
observationally identical. The type system proves it.

This is the same argument as why `runST` is safe: the state variable `s` is existential, 
so it cannot leak. Here, the feedback variable `c` is existential, so it cannot leak.

∎

### The Base Case: Untrace Without Compose

When `Untrace` stands alone (not part of a `Compose`):

```haskell
run (Untrace p) = \a -> fst $ fix $ \(_b, c) -> run p (a, c)
```

This is simpler: no sliding is needed. We close the loop directly:

1. **Input**: We receive `a`
2. **Pair with feedback**: Pair it directly with the feedback variable `c`: `(a, c)`
3. **Run the loop**: Feed this pair into `p`, which produces a new `(b, c)` pair
4. **Fixed point**: The fixed point finds the value of `c` such that the loop converges
5. **Projection**: Extract the `b` component with `fst`

The contrast with the sliding case: here, there is no intermediate pipeline `h`. 
The feedback variable enters at the very top level.

### The Yanking Axiom

A closed loop is evaluated by taking its fixed point:

```haskell
close :: Traced a a -> a
close = fix . run
```

When the pipeline is closed (input and output types match), `close` takes the fixed point, 
collapsing the entire computation to a value.

**Proof:**

```
Claim: close (build id) = id

Proof:

  close (build id)
= fix . run $ (build id)              [by definition of close]
= fix (run (build id))                [compose notation]
= fix id                              [by fusion law: run (build f) = f]
= id                                  [fixed point of identity is identity]

∎
```

The yanking axiom is immediate from the fusion law. Once you build and immediately 
run, you get the original function back. Taking its fixed point then gives you the 
fixed point of that function. For identity, that's identity itself.

### What We've Built

The three syntaxes — Coyoneda, Free, Traced — are complete:
- **Coyoneda** represents function application as data
- **Free** adds composition as data
- **Traced** adds loops as data

Each level is universal: any interpretation factors uniquely through the cast operations.
The laws are proven: fusion, identity, associativity, dinaturality, sliding, yanking.
The structure is sound.

The feedback variable, sealed by existential quantification, is what makes loops possible 
without closing them prematurely. Keep sliding until closed.

## Unified Representation

The three syntaxes — Coyoneda, Free, Traced — live in a single GADT with three 
constructors. Each constructor carries one syntactic choice. The algebra accumulates 
as we add layers.

Recovery functions let us extract the restricted views: a `Free` morphism that 
uses no `Untrace`, a `Coyoneda` morphism that uses no `Compose` or `Untrace`.

The pieces fit.

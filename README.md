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

**run**: Cast the syntax back to a function. When we see `Compose`, we collapse it.

```haskell
run :: Free a b -> (a -> b)
run Pure        = id
run (Apply f p) = f . run p
run (Compose g h) = run g . run h
```

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

**Associativity:** The algebra of function composition is associative. By casting, 
`Free` inherits this property.

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

**build**: Cast a function into Traced syntax (same as before).

```haskell
build :: (a -> b) -> Traced a b
build f = Apply f Pure
```

**run**: Cast the syntax back to a function. When we see `Untrace`, we close the loop.

```haskell
run :: Traced a b -> (a -> b)
run Pure          = id
run (Apply f p)   = f . run p
run (Compose g h) = run g . run h
run (Untrace p)   = \a -> fst $ fix $ \(_b, c) -> run p (a, c)
```

The `Untrace` case takes a fixed point over the pair `(b, c)`. The feedback loop is closed.

### The Sliding Law (Proved by Polymorphism)

When `Untrace` appears on the left of `Compose`, it slides inward, absorbing the 
right-hand side:

```
Untrace p ∘ g = Untrace (p ∘ (g × id_c))
```

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

### The Yanking Axiom

A closed loop is run by taking its fixed point:

```haskell
yank :: Traced a a -> a
yank = fix . run
```

When the pipeline is closed (input and output types match), `yank` takes the fixed point, 
collapsing the entire computation to a value.

### What We've Built

The three syntaxes — Coyoneda, Free, Traced — are complete:
- **Coyoneda** represents function application as data
- **Free** adds composition as data
- **Traced** adds loops as data

Each level is universal: any interpretation factors uniquely through the cast operations.
The laws are proven: fusion, identity, associativity, dinaturality, sliding, yanking.
The structure is sound.

The feedback variable, sealed by existential quantification, is what makes loops possible 
without closing them prematurely. Keep sliding until yanked.

## Unified Representation

The three syntaxes — Coyoneda, Free, Traced — live in a single GADT with three 
constructors. Each constructor carries one syntactic choice. The algebra accumulates 
as we add layers.

Recovery functions let us extract the restricted views: a `Free` morphism that 
uses no `Untrace`, a `Coyoneda` morphism that uses no `Compose` or `Untrace`.

The pieces fit.

⟝ hyperfunctions 

# Circuit.Hyper ⟜ Control.Monad.Hyper — A Comparative Analysis

Two libraries, same newtype, divergent designs. This document maps the shared
territory and the choices that separate them.

## The Shared Core

Both libraries define the same type:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

A hyperfunction from `a` to `b` is a function that, given a continuation from
`b` back to `a`, produces a `b`. The self-referential type wraps feedback into
the structure itself — the continuation carries the dual arrow, and composition
of hyperfunctions automatically threads feedback without explicit loop
constructs.

## The Divergence

| Aspect            | `Circuit.Hyper` (circuits)              | `Control.Monad.Hyper` (Kmett)         |
|-------------------|-----------------------------------------|---------------------------------------|
| **Encoding role** | Final object of traced monoidal cats    | Church encoding / final coalgebra     |
| **`run`**         | `invoke h (Hyper run)` — self-knot      | `invoke f id` — identity continuation |
| **Constant**      | `base`                                  | `pure`                                |
| **Embedding**     | `lift` (recursive)                      | `arr = fix . push`                    |
| **Observation**   | `lower`                                 | `project`                             |
| **Instances**     | Category, Semigroup, Monoid             | + Profunctor, Arrow, ArrowLoop        |
|                   | + Profunctor, Functor, Applicative (new)| + Functor, Applicative, Monad, Zip    |
| **Helpers**       | hyperAp, hyperBind, valueFix, hyperFix  | ana, cata, unroll, roll, fold, build  |
| **Dep chain**     | base + profunctors                      | base + profunctors + adjunctions + …  |

### `run` — Two Different Operations

This is the deepest difference:

```haskell
-- circuits: self-referential knot
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- Kmett: invoke with identity continuation
run :: Hyper a a -> a
run f = invoke f id
```

In circuits, `run` ties the hyperfunction to itself — a true fixed point.
`run (lift (+1))` diverges because `(+1)` has no fixed point.

In Kmett, `run (arr f) ≡ fix f` — the hyperfunction is invoked with the
identity hyperfunction as its continuation, which unfolds the computation.
`run (arr (+1))` also diverges, but via a different mechanism.

The difference matters when the continuation is non-trivial. Consider a
hyperfunction that inspects its continuation:

```haskell
-- This hyperfunction asks: "what would my continuation do with 5?"
query :: Hyper Int Int
query = Hyper $ \k -> invoke k (base 5)
```

Under circuits `run`: `run query` = `invoke (Hyper run) (base 5)` = 5.
Under Kmett `run`: `run query` = `invoke (arr id) (base 5)` = `project id 5` = 5.
Same result here, but the operational paths differ.

### `base` = `pure`

```haskell
-- circuits
base :: a -> Hyper b a
base a = Hyper (const a)

-- Kmett
pure :: a -> Hyper b a
pure a = Hyper $ \_ -> a
```

Identical. A hyperfunction that ignores feedback and returns a constant.

### `lift` = `arr`

```haskell
-- circuits (recursive)
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- Kmett (fixed-point)
arr :: (a -> b) -> Hyper a b
arr = fix . push
```

Both expand to `push f (push f (push f ...))` — an infinite stack of
function applications. Under lazy evaluation, each layer unwraps on demand.

### `lower` = `project`

```haskell
-- circuits
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (base a)

-- Kmett
project :: Hyper a b -> a -> b
project q x = invoke q (pure x)
```

Identical. Observe the hyperfunction by giving it a constant continuation.

## The Instance Landscape

### Before: "Hyper is invariant"

The original `Circuit.Hyper` claimed hyperfunctions admit no Functor,
Applicative, or Monad instances because `b` appears in both covariant
and contravariant positions:

```
invoke :: Hyper a b -> Hyper b a -> b
           ^covariant    ^b in 1st param (contravariant in invoke)
```

### After: Coinductive instances work

Kmett showed the way: define `Profunctor` with mutually recursive methods
that never structurally terminate, relying on laziness:

```haskell
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h   = Hyper $ invoke h . rmap f
  rmap f h   = Hyper $ f . invoke h . lmap f
```

`dimap` calls itself — the hyperfunction's continuation is itself a `dimap`
of the original continuation. `lmap` and `rmap` call each other in a mutual
recursion that never bottoms out.

This is **sound** under lazy evaluation: any finite observation (via `lower`
or `run`) will only unfold finitely many layers, never reaching bottom.

From `Profunctor` we get `Functor` for free:

```haskell
instance Functor (Hyper a) where
  fmap = rmap
```

And `Applicative` via the anamorphism:

```haskell
instance Applicative (Hyper a) where
  pure = base
  p <* _ = p
  _ *> p = p
  (<*>) = curry $ ana $ \(i, j) fga ->
    unroll i (\i' -> fga (i', j)) $ unroll j (\j' -> fga (i, j'))
```

### Why not Monad?

Kmett provides `Monad (Hyper a)` via catamorphism:

```haskell
instance Monad (Hyper a) where
  return = pure
  m >>= f = cata (\g -> roll $ \k -> unroll (f (g k)) k) m
```

Circuit.Hyper omits this instance to keep the surface area small.
`hyperBind` serves as the stand-alone equivalent:

```haskell
hyperBind :: Hyper a b -> (b -> Hyper a c) -> Hyper a c
hyperBind m k = lift $ \a -> lower (k (lower m a)) a
```

The key difference: `hyperBind` observes through `lower` and rebuilds with
`lift`, losing any internal feedback structure. The `Monad` instance preserves
the coinductive structure but is harder to reason about.

## The fold/build Pattern

Kmett's library includes a classic fold/build fusion system adapted to
hyperfunctions:

```haskell
fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold []     _ n = pure n
fold (x:xs) c n = push (c x) (fold xs c n)

build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])
```

This is Church encoding of lists via hyperfunctions. `fold` materialises a
list into a hyperfunction; `build` extracts a list by running the
hyperfunction with `(:)` as the combinator. The fusion law `fold . build ≡ id`
holds under "nice conditions" (the hyperfunction must be parametric).

In Circuit.Hyper, the same pattern is expressible directly:

```haskell
foldC :: [a] -> (a -> b -> c) -> c -> Hyper b c
foldC [] _ n = base n
foldC (x:xs) c n = push (c x) (foldC xs c n)

buildC :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
buildC g = run (g (:) [])
```

Example:

```
>>> buildC (\c n -> foldC [1,2,3] c n)
[1,2,3]
```

## Recursion Patterns Compared

### Fixed-point recursion

```haskell
-- circuits: hyperFix (structural fix at Hyper level)
hyperFix :: (Hyper a a -> Hyper a a) -> Hyper a a
hyperFix = fix

-- Usage: factorial
fact :: Hyper Int Int
fact = hyperFix $ \f -> lift $ \n ->
  if n == 0 then 1 else n * lower f (n - 1)
```

In both libraries, `fix` at the `Hyper` level works because `Hyper a a` is
a coinductive type — the fixed point is a productive infinite structure.

### Value recursion

```haskell
-- circuits: valueFix (fix at the output value)
valueFix :: (b -> Hyper a b) -> Hyper a b
valueFix f = lift $ \a -> fix $ \b -> lower (f b) a

-- Usage: constant stream 1,1,1,...
ones :: Hyper () [Int]
ones = valueFix $ \xs -> lift $ \_ -> 1 : xs
```

This is equivalent to Kmett's approach where `MonadFix` on hyperfunctions
enables `mfix`-style recursion.

### Anamorphism / Catamorphism

Kmett's `ana` and `cata` are now available in Circuit.Hyper:

```haskell
-- Unfold a hyperfunction from state
counter :: Int -> Hyper Int Int
counter = ana $ \i self -> (i, self (i + 1))

-- Fold a hyperfunction to a value
summarise :: Hyper a b -> ???
```

The anamorphism builds a hyperfunction by threading state; the catamorphism
consumes one. Together they form the universal construction for hyperfunctions
as a final coalgebra.

## Example: Stream Processing

Both libraries can express stream processing, but the idioms differ:

```haskell
-- Circuit.Hyper style: use lift + combinators
process :: Hyper [Int] [Int]
process = lift (map (+1)) ⊙ lift (filter even)

-- Kmett style: use Arrow syntax
process :: Hyper [Int] [Int]
process = arr (map (+1)) >>> arr (filter even)
```

With the new `Profunctor` instance, Circuit.Hyper also gains `dimap` for
pre/post-processing:

```haskell
-- Pre-process input, run hyperfunction, post-process output
pipeline :: Hyper String String
pipeline = dimap words unwords (lift (map reverse))
```

## The Philosophical Tension

Circuit.Hyper originally claimed "Hyper is invariant… does not admit Functor,
Applicative, or Monad instances." This is **nominally true** — the type
parameter `b` appears in both covariant and contravariant positions in the
unfolding of `invoke`. A strict language would indeed reject `Functor`.

Kmett's instances are **coinductively true** — they work because lazy
evaluation only forces finitely many layers. Each `fmap` application wraps
another coinductive layer rather than structurally transforming the type.

The `Circuit.Hyper` module now provides both perspectives:
- The Profunctor/Functor/Applicative instances for those who want the Kmett
  style
- The `hyperAp`/`hyperBind`/`valueFix`/`hyperFix` combinators for those who
  prefer explicit observation-and-rebuilding

This reflects a broader pattern in the circuits library: **the initial
encoding (Circuit GADT) is the ground truth** — Functor, Applicative, Monad
are straightforward structural instances. **The final encoding (Hyper) is
the semantic reflection** — it compresses feedback into the type, and
instances become coinductive loops rather than structural recursion.

## References

- [Zip fusion with Hyperfunctions](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.36.4961&rep=rep1&type=pdf)
- [Categories of processes enriched in final coalgebras](https://link.springer.com/chapter/10.1007/3-540-45315-6_20)
- [Seemingly Impossible functional programs](http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/)
- [Hyperfunctions by Donnacha Oisín Kidney](https://doisinkidney.com/posts/2021-03-14-hyperfunctions.html)
- Kmett, E. (2015). Control.Monad.Hyper

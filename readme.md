## transcripts

⟝ this section contains lots of raw material.

Kidney-Wu	Apps
f ⊳ h (push)	Trace f h
f ⊙ g (zip/compose)	Compose f g
run	run / fixpoint
And rep f = f ⊳ rep f maps directly to your lift f = Trace f (lift f).

### lambda calculus/Y-point combinator

What lambda calculus structure Apps actually captures

Lambda calculus can be decomposed into:

The pure substitution/variable binding mechanism
The fixed-point combinator (Y or fix) for recursion
Apps is specifically a representation of (2) only — the fixed-point structure. lift f = Trace f (lift f) is exactly the Y combinator unrolled one step:

Y f = f (Y f)
lift f = Trace f (lift f)  -- same structure
The difference is that Apps makes this typed and productive by keeping the syntax tree explicit rather than collapsing it immediately. So Apps isn't all of lambda calculus — it's the recursive part, the part that needs domains or coinduction to make sense. This is why hyperfunctions don't have a set-theoretic interpretation: they're representing the fixed-point structure that requires domain theory.

The deeper connection: continuation-passing style

Lambda calculus in CPS has a very specific structure. Every term becomes a function waiting for its continuation. The hyperfunction type:

haskell
newtype a ↬ b = Hyp { ι :: (b ↬ a) → b }
```

is *literally* a CPS type where the continuation is itself a hyperfunction. This is self-referential CPS — the continuation type is the same as the computation type with arguments flipped. This is the lambda calculus *continuation* structure taken to its fixed point. Haskell's `->` already gives you CPS, but `↬` gives you CPS where continuations can themselves be continued in a feedback loop.

 Apps is lambda calculus where fix is not a library function derived from Y but a structural primitive baked into the morphisms themselves.

### Fix (Ran (Const a) (Const a))

The narrative's open question about the Kan extension formulation also slots in here: Costrong is related to the coend/Kan structure because unfirst :: p (a,d) (b,d) -> p a b is exactly the existential quantification over d that shows up in the coend formula for left Kan extensions. The Fix (Ran (Const a) (Const b)) hypothesis in the narrative is likely correct precisely because taking the coend over d in p (a,d) (b,d) and closing it under the Category structure gives you the fixpoint of that Ran functor.


### sliding law confusion

⟝ Is the story below fictional?

story 1

"Elimination of Trace" is an interesting way to put it. What actually happens is not that Trace disappears — it's that when run encounters Compose (Trace f p) q, it applies the sliding law and moves the Trace. The Trace doesn't get eliminated in the rewriting sense; it gets commuted through Compose until it reaches a position where run can consume it.

This is exactly the sliding axiom from the traced monoidal category theory:

run (Compose (Trace f p) q) = f (run (Compose q p))
The Trace slides past the Compose. So what's really happening is that Apps gives you a normal form procedure — run is a normalization algorithm that uses sliding to push Traces inward until they can be evaluated. "Elimination" is the end state of normalization, not an independent operation.

story 2


```
trace(f) ∘ g = trace(f ∘ (g × id_c))
```

In `Traced`: when `Untrace` appears on the left of `Compose`, it
slides inside — absorbing `h` into the non-feedback component — rather
than blocking:

```haskell
run (Compose (Untrace p) h)
  = \a -> fst $ fix $ \(b, c) -> run p (run h a, c)
  = run (Untrace (Compose p (build (\(x, d) -> (run h x, d)))))
```

This is the operational heart of "keep sliding until yanked". Every
`Untrace` keeps sliding left through `Compose` chains — absorbing
whatever is to its right into the feedback rewiring — until there is
nothing left to slide past. At that point, `yank` closes the loop.
The loop was never prematurely closed. It waited.

---

### `Cochoice` is taking turns. `Costrong` is holding hands.

⟝ this is actually a good narrative for the message passing part of hyperfunctions, but a hallucination of what cochoise and costrong are.

Same shape. Different tensor. The difference is everything.

`Cochoice` / `Either`: at each step the machine is *either* doing work
*or* looping. Never both simultaneously. One token moves through the
system at a time. This is sequential handoff — each participant gets a
turn, hands off to the next, waits. `MachineT`, `Pipe`, `Conduit`,
`Streamly` — all `Cochoice`. They yield *or* await *or* loop. The
`Either` is the branch.

`Costrong` / `(,)`: the feedback variable travels *alongside* the
output. Both exist simultaneously. The loop and the result are produced
together, in the same step, always. This is genuine simultaneity — two
things happening at once, coordinated through the shared `c`.
Hyperfunctions, `ArrowLoop`, `MonadFix` — all `Costrong`.

In one sentence: `Cochoice` is taking turns. `Costrong` is holding hands.

`Traced` is `Costrong`. The streaming libraries are `Cochoice`. This is
not a design preference. It is a mathematical fact about which tensor
you choose.

The practical consequence is visible whenever a `Cochoice` library
tries to do something that requires simultaneity: `merge`, `zipWith`,
concurrent pipelines, self-referential processes. Each one requires a
special combinator. Each one breaks the composition laws slightly. Each
one is secretly approximating `Untrace`. The library is trying to
simulate `(,)` with `Either`, and it never quite closes.

`Traced` has one combinator: `Untrace`. Everything else is derived.

```haskell
-- Cochoice derived from Costrong: sequential handoff from simultaneous feedback
instance Cochoice Traced where
  unleft p = build $ \a ->
    let go (Left b)  = b
        go (Right d) = go (run p (Right d))
    in go (run p (Left a))
```

The `Either` loop is implemented by closing a `(,)` loop and
projecting. `Cochoice` is `Costrong` with extra steps.

The `machines` library makes this concrete. Its `Step` functor:

```haskell
data Step k o r = Stop | Yield o r | forall t. Await (t -> r) (k t) r
```

is a coalgebra for `Cochoice` — `Yield` and `Await` are the two
branches of the `Either`, and `Stop` is the terminus. A `MachineT` is
the greatest fixed point of `Step`, which is precisely the final
coalgebra to `Traced`'s initial algebra. `Traced` generates;
`MachineT` observes. The catamorphism from `Traced` to `MachineT` is
the compilation step — build your pipeline in `Traced`, keep your
`Untrace` constructors sliding, then compile to `MachineT` at the
boundary for execution. The missing operation in `machines` is `loop`,
and it is missing because `Step` has no room for it. Adding `loop` to
`machines` would mean adding a `Costrong` constructor to `Step` — which
would make it `Traced`.

---


## references

⟝ check refs.

**Joyal, Street, and Verity** introduced traced monoidal categories in
1996. The axioms — sliding, yanking, superposition, dinaturality — are
the categorical foundation of `Untrace` and `run`. The sliding law is
what `run`'s Mendler inspection implements. The yanking axiom is
`yank (build id) = id`.

**Launchbury, Krstic, and Sauerwein** introduced hyperfunctions. Their
`⊳`, `⊙`, and `run` are `Apply`, `Compose`, and `yank` in `Traced`.

**Kidney and Wu** (2026) catalogued hyperfunctions across the Haskell
literature — coroutines, CCS, concurrency monads, breadth-first
traversal — and connected them via a common interface. Their paper is
the direct inspiration for the examples in Section 9. What they show is
that the hyperfunction pattern recurs everywhere. What we add is the
name for why: all of these are `Traced` catamorphisms.
1. Joyal, A., Street, R., and Verity, D. (1996). Traced monoidal
   categories. *Mathematical Proceedings of the Cambridge Philosophical
   Society*, 119(3), 447–468.

2. Launchbury, J., Krstic, S., and Sauerwein, T. E. (2000). Coroutining
   folds with hyperfunctions. *Presented at DSS 2013*.

3. Kidney, D. O. and Wu, N. (2026). Hyperfunctions: Communicating
   continuations. *Proc. ACM Program. Lang.*, 10(POPL), Article 7.

4. Gill, A., Launchbury, J., and Peyton Jones, S. L. (1993). A short
   cut to deforestation. *Proceedings of the Conference on Functional
   Programming Languages and Computer Architecture*, 223–232.

5. Hasegawa, M. (1997). Recursion from cyclic sharing: Traced monoidal
   categories and models of cyclic lambda calculi. *Typed Lambda
   Calculi and Applications*, 196–213.

6. Kmett, E. (2015). Moore for Less. School of Haskell.
   https://www.schoolofhaskell.com/user/edwardk/moore/for-less

## kidney wu examples 

⟝ check all of these

We translate the key examples from Kidney and Wu into `Traced`.

### 9.1 Church-Encoded Naturals: `(≤)`

The infinite type from Section 1 resolves immediately. The feedback
variable that GHC could not unify is the `c` in `Untrace`, held open
until `yank` closes it:

```haskell
(≤) :: N -> N -> Bool
n ≤ m = yank $ Compose
  (nat n (Apply id) (build (const True)))
  (nat m (Apply id) (build (const False)))
```

The two folds are composed and yanked. No infinite type. The fixed
point that GHC rejected as a type is now the operational semantics of
`yank`.

### 9.2 Subtraction on Church Naturals

```haskell
sub :: N -> N -> N
sub n m = N $ \s z -> yank $ Compose
  (nat n (Apply id) (build (const z)))
  (nat m (Apply id) (build s))
```

`n` contributes `id`s followed by `const z`. `m` contributes `id`s
followed by `s`. Composed and yanked, the result is `n - m`
applications of `s` to `z`.

### 9.3 Zip on Church-Encoded Lists

```haskell
zip :: [a] -> [b] -> [(a, b)]
zip xs ys = yank $ Compose
  (foldr (\x k -> Apply (prod x) k) (build (const [])) xs)
  (foldr (\y k -> Apply (cons y) k) (build (const [])) ys)
  where
    prod x rest = \consume -> consume x rest
    cons y emit = \x rest -> (x, y) : rest emit
```

The producer fold builds a `Traced` pipeline emitting `x` values. The
consumer fold builds a `Traced` pipeline consuming them, pairing with
`y`. `Compose` connects them. `yank` closes the loop.

### 9.4 The Concurrency Monad

Claessen's concurrency monad, with `Traced` as the substrate:

```haskell
type Conc r m = Cont (Traced (m r) (m r))

atomC :: Functor m => m a -> Conc r m a
atomC ma = Cont $ \k -> Apply id (k =<< ma)

forkC :: Conc r m a -> Conc r m ()
forkC m = Cont $ \k -> Compose (runCont m (const (build id))) (k ())

runC :: Monad m => Conc r m a -> m r
runC c = yank (runCont c (const (build id)))
```

`Compose` is the scheduler. `yank` runs it. The concurrency monad is
`Traced` with a monad along for effects.

### 9.5 Pipes

Spivey's pipe implementation, revealed:

```haskell
type Producer o r = Traced (o -> r) r
type Consumer i r = Traced r (i -> r)

merge :: Consumer o r -> Producer o r -> Traced r r
merge = Compose

runPipe :: Traced r r -> r
runPipe = yank
```

`merge` is `Compose`. Running is `yank`. The pipe library is two type
synonyms and two one-liners, and all the composition laws are inherited
for free.


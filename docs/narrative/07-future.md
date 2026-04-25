# Where We Go Next

**Status:** Draft  
**Prev:** [06-rwr.md](06-rwr.md)

---

`Circuit` is the free traced monoidal category. `Hyper` is its final encoding. The two adjunctions and the sliding axiom are in place. What can you build with this?

---

## Production Patterns

### Bidirectional Pipes

The `(,)` tensor with `Kleisli IO` gives bidirectional pipes: processes that produce and consume simultaneously, with feedback threading state through the loop.

```haskell
-- A pipe that echoes input and counts steps
counter :: Circuit (Kleisli IO) (,) Int Int
counter = Loop $ \(n, x) -> do
  putStrLn $ "step " ++ show n ++ ": " ++ show x
  pure (n + 1, x)
```

The `(,)` feedback carries the count; the output passes the value through. The loop runs indefinitely, threading state without explicit mutation.

### State Machines

The `Either` tensor gives state machines: processes that iterate until a termination condition, with `Left` meaning "continue" and `Right` meaning "done".

```haskell
-- A machine that counts to n then stops
countdown :: Int -> Circuit (->) Either () ()
countdown n = Loop $ \case
  Left  k | k > 0 -> Left  (k - 1)
  _               -> Right ()
```

The `Either` feedback carries the counter. The machine iterates `n` times then terminates with `Right ()`.

### Self-Referential Streams

`Hyper` with `(,)` models self-referential streams — streams that feed back into themselves. The Fibonacci example from [Section 1](01-stack-language.md) is the canonical case. More complex examples: breadth-first tree traversal, concurrent scheduler, backpropagation through a neural network.

### Parsers

The `Either` tensor with backtracking gives parsers: a `Left` result means "failed, try the next alternative"; a `Right` result means "succeeded, return the parse tree". The `Loop` constructor builds recursive grammars. The `Mendler case` ensures that left-recursive grammars are handled correctly.

### Agents

`Circuit (Kleisli IO) (,) Observation Action` is an agent: an IO process that takes observations and produces actions, with feedback threading the agent's internal state through the loop.

```haskell
type Agent state obs action = Circuit (Kleisli IO) (,) obs action
```

The `(,)` feedback carries the state. The agent loop runs indefinitely. The `Loop` constructor is where the state update lives.

---

## Open Mathematical Questions

Several questions from the development are unresolved:

**1. Kan isomorphism (formal)**

The observation `Circuit a b ~ Ran (Const a) (Const b)` (before `Fix`) is a diagram observation, not a theorem. The precise isomorphism needs to be established.

**2. Uniqueness of `Loop`**

`toHyper` is a traced functor from `Circuit` to `Hyper`. Is it the *unique* traced functor? The freeness of `Circuit` as a traced monoidal category depends on this. The argument exists informally; it needs to be formalised.

**3. Fix(Circuit) isomorphism**

Is `Hyper a b ~ Fix (Circuit (->) t a b)` an isomorphism or a strict inequality? `toHyper` exists and the triangle holds, but `flatten` is lossy — the two encodings are not isomorphic on the nose. The precise adjunction needs to be stated.

**4. Mendler case as counit naturality**

The Mendler case enforces the sliding axiom. Is it exactly the counit naturality of `Ran (Const a) (Const b)`, formalised? This would close the loop between the operational description and the categorical one.

**5. Geometry of Interaction**

The `Int(C)` completion, `callCC`, `shift/reset` — the connection to the Geometry of Interaction is a conjecture, not yet developed. `Hyper` looks like it should fit into the GoI framework; the precise connection is open.

---

## Extensions

### Graded Circuits

A graded version would count `Loop` depth as a grade. This would give finer control over the feedback structure and map onto Okasaki's amortised queue analysis — the grading tracks how many levels of `viewl` are needed.

### More Effects

`Circuit (Kleisli m) t` works for any monad `m` with a suitable `Trace` instance. The current `Kleisli IO` instance uses delimited continuations (`prompt`, `control0`). Other monads — `State`, `Writer`, `Except` — need their own `Trace` instances, which may require additional structure on `m`.

### Profunctor Optics

`Circuit` is already a profunctor. The connection to profunctor optics (lenses, prisms, traversals) is direct: optics are exactly the morphisms in categories of profunctors. `Circuit` with `(,)` gives a traced version of `Strong`; with `Either` a traced version of `Choice`. This suggests a library of traced optics built on `Circuit`.

### Learner Integration

The learners paper ([buff/learners-full.md](../../mg/buff/learners-full.md)) shows that the category of extensional learners is almost compact closed — it needs one quotient. `Circuit` is the free traced monoidal category; `AtempC` (atemporal learners) is the free compact closed category. The connection is the theorem that compact closed = traced + duals. Implementing this in Haskell would give a library of bidirectional, backpropagating, compact-closed circuits.

---

## How to Contribute

### Add an Example

The `examples/` directory contains existing patterns (Agent, Dual, Parser). A good new example:

1. Picks one of the production patterns above
2. Is self-contained (compiles without external dependencies)
3. Has a doctest showing the input/output
4. Links back to the relevant narrative section

### Add a Trace Instance

A new `Trace` instance for a tensor `t`:

1. Define `trace` and `untrace` for the new `t`
2. Prove (or argue) the sliding axiom: `trace (f . untrace g) = trace f . g`
3. Add a doctest showing a non-trivial `Circuit` over the new `t`

### Formalise an Open Question

Pick one of the open questions above. Any progress — even a sketch or a counterexample — is valuable.

---

## The Slogan, Revisited

> **Two adjunctions plus one strength.**

By this point the slogan has a full meaning:

- **Free / forgetful** (`Lift ⊣ lower`) — category structure, most axioms
- **Initial / final** (`Circuit ↔ Hyper`) — the two encodings; universal property
- **Sliding axiom** — the one honest traced-category content

And the performance corollary:

> **Amortise via the final encoding.**

Build in `Circuit`. Inspect in `Circuit`. Run in `Hyper`. The Mendler case is the bridge — it makes the sliding axiom operational, which is what `toHyper` then amortises away.

---

## References

- Kidney & Wu (2026) — breadth-first search, concurrency scheduler, producer/consumer
- Riley (2025) — learners and compact closed categories; [buff/learners-full.md](../../mg/buff/learners-full.md)
- Van der Ploeg & Kiselyov (2014) — Reflection Without Remorse
- Hasegawa (1997) — Geometry of Interaction connection (conjecture)
- [circuit-categorical.md](../../mg/buff/circuit-categorical.md) — categorical shopping list

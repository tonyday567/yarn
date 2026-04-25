# The Tensor Parameter: Holding Hands vs Taking Turns

**Status:** Draft  
**Prev:** [04-hyper.md](04-hyper.md) | **Next:** [06-rwr.md](06-rwr.md)

---

`Circuit arr t a b` is generic over the tensor `t`. This is not a technical convenience — it is an operational choice. The two primary tensors `(,)` and `Either` give fundamentally different semantics for feedback, and choosing between them is a design decision about how processes communicate.

---

## The Trace Typeclass

The tensor `t` must carry a `Trace` instance:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `arr = (->)`:

| Tensor `t` | `trace`    | `untrace`  | Character       |
|------------|------------|------------|-----------------|
| `(,)`      | `unsecond` | `second`   | Simultaneous    |
| `Either`   | `unright`  | `fmap`     | Sequential      |

The `Loop` constructor is the same in both cases. What changes is how the feedback channel behaves when `trace` closes it.

---

## (,) — Holding Hands

With `t = (,)`, `trace` is `unsecond`:

```haskell
trace f b = let (a, c) = f (a, b) in c
```

The feedback value `a` and the output `c` are produced simultaneously. Both sides of the tensor progress lock-step. The loop ties a **lazy knot**: `a` feeds back into itself, and Haskell's lazy evaluation unrolls it productively.

**Operational character:**
- Feedback and output exist in parallel
- Both sides progress simultaneously
- Suitable for: dataflow, stream processing, zipping, true concurrency

**When it works:** When the feedback can be consumed lazily — when the output of one step does not need to be fully evaluated before the next step can begin.

**When it fails:** When the computation requires strict evaluation and the feedback forms a cycle that cannot be unrolled productively. This is the `let` in `trace` — it is a lazy fixpoint.

The Fibonacci example uses `(,)`:

```haskell
fibs = Loop (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
```

The feedback channel carries the stream. The stream feeds back into itself via lazy `zipWith`. This works because list cons is lazy — `0 :` forces nothing before it is needed.

---

## Either — Taking Turns

With `t = Either`, `trace` is `unright`:

```haskell
trace f b = case f (Right b) of
  Left a  -> trace f a   -- iterate: feedback to self
  Right c -> c           -- done: produce output
```

The feedback value (Left) and the output (Right) take turns. Only one participant acts per step. The loop iterates until a `Right` is produced.

**Operational character:**
- Feedback and output are sequential
- Only one side acts per step
- Suitable for: coroutines, schedulers, state machines, parsers with backtracking

**When it works:** When the computation is naturally iterative — when each step is either "not done yet" (Left, continue) or "done" (Right, output).

**The difference from `(,)`:** With `(,)`, the feedback is always present alongside the output. With `Either`, the feedback and output are exclusive — you get one or the other on each step. This is exactly the difference between a concurrent process (both running) and a coroutine (taking turns).

---

## The Kidney–Wu Insight

Kidney & Wu (2026) observe that the producer/consumer pattern decomposes:

- A **simultaneous** `(,)` process can be split into two **sequential** `Either` processes that communicate via message passing.

This is why the hyperfunction type `Hyper a b` — which threads both directions through a single self-referential type — unifies the two tensor perspectives through the duality of the continuation channel.

Every effects library that tries to do simultaneity on top of `Either` (merge, zipWith, concurrent pipelines, self-referential processes) is approximating `Costrong` with `Cochoice`. Each requires special combinators and breaks composition slightly.

`Circuit` with `(,)` has one combinator: `Loop`. Everything else is derived.

---

## Costrong vs Cochoice

The categorical names for the two tensor characters:

| Tensor | Typeclass | Pattern | Use case |
|--------|-----------|---------|----------|
| `(,)` | `Costrong` | Holding hands | Dataflow, zipping, concurrency |
| `Either` | `Cochoice` | Taking turns | Coroutines, schedulers, parsers |

Hasegawa's distinction between cartesian traces (fixed points directly, `(,)`) and computational traces (via sequential handoff, `Either`) explains why these are semantically different, not just technically:

- **Costrong:** Both sides progress lock-step. Hasegawa's cartesian traces.
- **Cochoice:** Sequential handoff. Hasegawa's computational traces with asymmetric sharing.

In a cartesian traced category (`(,)` tensor), Hasegawa's Theorem 3.1 shows that traces and fixed-point operators coincide — `run (lift f) = fix f` is a theorem, not an axiom. In the cochoice case (`Either`), the trace is strictly more general than a fixed-point operator.

---

## Kleisli IO via Delimited Continuations

Both tensors extend to `Kleisli IO` via delimited continuations:

```haskell
instance Trace (Kleisli IO) (,)     where ...
instance Trace (Kleisli IO) Either  where ...
```

The `(,)` instance uses `prompt` and `control0` to implement a lazy knot in IO. The `Either` instance iterates with `prompt` until a `Right` is produced.

This gives `Circuit (Kleisli IO) t a b` — effectful circuits. The `Loop` constructor runs IO actions in a feedback loop, with the tensor choice controlling how the IO actions are interleaved.

---

## Choosing a Tensor

The choice of tensor is a design decision:

**Use `(,)` when:**
- Processing streams or dataflows
- Processes need to run concurrently and share state
- The feedback is consumed lazily (e.g., lists, streams)
- You want the producer/consumer pattern

**Use `Either` when:**
- Implementing coroutines or state machines
- The computation iterates until a termination condition
- You want strict, sequential feedback (e.g., parsers, schedulers)
- You need to reason about termination

---

## The Circuit is Generic; the Choice is Yours

The `Circuit` GADT is identical for both tensors. The `Loop` constructor is the same. The `lower` interpreter is the same (modulo the `Trace` instance). The difference is entirely in the `Trace` instance — in what `trace` and `untrace` mean.

This is the point of parametrising over `t`. The categorical structure — the free traced monoidal category — is the same. The operational character — simultaneous or sequential — is a choice made at the instance level.

---

## Summary

| | `(,)` | `Either` |
|--|-------|---------|
| Character | Simultaneous / holding hands | Sequential / taking turns |
| `trace` | Lazy lazy knot (`unsecond`) | While-loop (`unright`) |
| `untrace` | `second` | `fmap Right` |
| Use case | Streams, concurrency, dataflow | Coroutines, parsers, schedulers |
| Categorical name | Costrong | Cochoice |

**Next:** [06-rwr.md](06-rwr.md) — Reflection Without Remorse; the Mendler case as `viewl`; performance story.

---

## References

- Kidney & Wu (2026) — producer/consumer insight; both tensor instances
- Hasegawa (1997) — cartesian vs computational traces; [hasegawa.md](../other/hasegawa.md)
- [axioms-traced.md](../other/axioms-traced.md) — proofs for both `(,)` and `Either` instances

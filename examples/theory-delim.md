
https://ghc-proposals.readthedocs.io/en/latest/proposals/0313-delimited-continuation-primops.html

## evaluation contexts and reduction rules

Lexi's key move is the evaluation context `E[e]` — a syntactic frame with a hole. `catch` and `throw` are given by two reduction rules:

```
catch (pure v) f       ⟶  pure v
catch E[throw e] f     ⟶  f e
```

The delimiter (`reset`/`catch`) marks the boundary of the captured continuation. `shift`/`throw` captures everything up to the nearest delimiter and no further. The `r` parameter in `DCont r a` tracks the result type of the nearest `reset` — it changes when you enter a new delimiter scope.

---

## the correspondence

| delimited continuations | Circuit |
|---|---|
| `reset` / `catch` | `Loop` |
| `shift` / `throw` | `untrace` |
| boundary collapse | `trace` |
| evaluation context `E[●]` | `Compose _ g` — the hole is the feedback channel |
| `r` in `DCont r a` | tensor `t` in `Circuit arr t a b` |
| `forall r` in `reset :: DCont a a -> DCont r a` | `forall a` in `Loop :: arr (t a b) (t a c)` |

The Mendler case:

```haskell
run (Compose (Loop f) g) = trace (f . untrace (run g))
```

is the reduction rule `catch E[throw e] f ⟶ f e` — `Loop` playing `catch`, `run g` playing the evaluation context `E`, `untrace` injecting into the hole, `trace` collapsing the boundary.

---

## the type-level tracking

In `DCont r a`, `r` is universally quantified at `reset` but fixed by the enclosing context — the delimiter scope is opaque to what is outside it. Two computations inside the same `reset` share the same `r`; crossing a `reset` boundary changes `r`.

In `Circuit arr t a b`, `t` plays the same role. `forall a` in `Loop :: arr (t a b) (t a c)` is the statement that the channel type `a` is opaque to what is outside the loop — the feedback scope is sealed. `trace` and `untrace` are the only operations that cross the boundary, exactly as `shift` and `reset` are the only operations that cross the delimiter.

---

## fix cancellation revisited

This is where the connection earns its keep. Act 1 cancelled fix from:

```
fix (ε (η f ⊙ (p ⊙ q)))  =  fix (f . ε (q ⊙ p))
```

The cancellation requires that the two fixpoints are the same fixpoint — same type, same scope. In delimited continuation terms: both sides are inside the same `reset`, so they share the same `r`. The delimiter is the guarantee that `fix x = fix y ⟹ x = y` holds here.

`Loop` is that delimiter. The tensor `t` and `forall a` are its type-level witness. The cancellation is valid because `Loop` seals the scope — the fixpoint cannot escape or be confused with a fixpoint from another scope.

---

## not an analogy

The `r` parameter in `DCont` and the tensor `t` in `Circuit` are the same type-level mechanism: tracking the result type of the nearest delimiter, universally quantified at the boundary, fixed within the scope. The reduction rule for `catch E[throw e]` and the Mendler case for `run (Compose (Loop f) g)` are the same rule: extract what is inside the delimiter, apply the boundary operation, continue.

This is not a structural resemblance. It is the same thing.

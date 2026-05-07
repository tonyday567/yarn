# Pipes — Proxy decomposition

The `Proxy` type from Gabriel Gonzalez's `pipes` library decomposes into
Circuit tensors. The key is the repeated elimination pattern — every
instance follows the same Mendler fold.

## The Proxy type (simplified)

```haskell
data Proxy a' a b' b m r
    = Request a' (a  -> Proxy a' a b' b m r)  -- send a' downstream, await a
    | Respond b  (b' -> Proxy a' a b' b m r)  -- send b upstream,  await b'
    | M          (m    (Proxy a' a b' b m r)) -- monadic interleaving
    | Pure    r                               -- done
```

Four type parameters encode two bidirectional channels:

| parameter | direction  | role                              |
|----------|-----------|-----------------------------------|
| `a'`     | downstream| what we request                   |
| `a`      | upstream  | what we receive in response       |
| `b`      | upstream  | what we respond with              |
| `b'`     | downstream| what we receive as next request   |

## The universal eliminator

Every Proxy instance follows the same structural recursion — 13 times
through `fmap`, `<*>`, `>>=`, `<>`, `hoist`, `embed`, `local`, `listen`,
`pass`, `catchError`, `catch`:

```haskell
go p = case p of
    Request a' fa  -> Request a' (\a  -> go (fa  a ))  -- thread through cont
    Respond b  fb' -> Respond b  (\b' -> go (fb' b'))  -- thread through cont
    M          m   -> M (go <$> m)                      -- map through monad
    Pure    r      -> <instance-specific base case>
```

This is `cata` for the Proxy pattern functor. The `go . fa` is
hyperfunction `push` — threading the fold through the continuation slot.

## Decomposition into tensors

Strip the monad and look at the structure:

```
ProxyF a' a b' b r
    = Either (a', a → r) (b, b' → r)
```

Each branch is a `(,)` of `(payload, continuation_slot)`. The outer
`Either` chooses direction. In Circuit:

```haskell
-- the Proxy pattern as a Circuit tensor structure
type ProxyCircuit a' a b' b r =
    Circuit (->) Either (a', a → r) (b, b' → r)
```

Where:
- `Either` tensor chooses Request vs Respond (direction)
- `(,)` in each branch carries payload + continuation slot
- `Loop` ties the fixed point (the recursion over the continuation)

With monadic effects:

```haskell
type ProxyCircuitM m a' a b' b r =
    Circuit (Kleisli m) Either (a', a) (b, b')
```

The `r` parameter is the exit type — what `Pure` returns. The `M`
constructor is `Lift` in the `Kleisli m` arrow.

## The channel connection

Before the full Proxy, the single-channel case is `Hyper (i → s) (o → s)`:

```haskell
-- one direction: consume i, produce o, parameterised by answer type s
Channel i o s = Hyper (i -> s) (o -> s)
```

This is the Kidney Wu `Hyp (o → a) (i → a)` in our notation. `invoke` on a
channel:

```haskell
invoke :: Channel i o s -> Channel o i s -> (o -> s)
--         channel           dual channel       output function
```

The dual channel has swapped directions — consume o, produce i. Applying
`invoke` with the dual gives the output function `o → s`. This is the
coroutine handoff: yield `o`, await `i`, parameterised by answer `s`.

The Proxy is the bidirectional version — two channels, dual to each other:
- Channel `(a', a)` going downstream (request channel)
- Channel `(b, b')` going upstream (response channel)

When `b' = a` and `b = a'`, the two channels are mutual duals — what one
sends, the other receives.

## Compact closed hint

`Request (a', a → r)` and `Respond (b, b' → r)` are dual. Swap parameters:
`Request` with `(a' ↔ b')` and `(a ↔ b)` gives `Respond`. In a compact
closed category:

- `Request` is the unit `η : I → A* ⊗ A` of the downstream dual pair
- `Respond` is the counit `ε : B ⊗ B* → I` of the upstream dual pair

When `A = B*` and `A* = B` (the channels are mutual duals), Proxy becomes
a bidirectional pipe in a compact closed category.

The `Dual` constructor from the Back GADT makes this explicit:

```haskell
data Back arr t a b where
  Lift    :: arr a b -> Back arr t a b
  Compose :: Back arr t b c -> Back arr t a b -> Back arr t a c
  Loop    :: arr (t a b) (t a c) -> Back arr t b c
  Dual    :: Back arr t a b -> Back arr t b a          -- flip direction

-- Request and Respond are duals under the appropriate swap
-- Dual (Request a' (a -> r)) ≅ Respond a' (a -> r) with swapped roles
```

The `Dual` constructor makes the symmetry structural: `Dual (Dual f) = f`,
`runFwd (Dual f) = runBwd f`. A Proxy with explicit duality would look
like:

```haskell
type BidirectionalPipe m i o r = 
    Back (Kleisli m) Either (i, o) (o, i)
    -- Left = Request direction, Right = Respond direction
    -- Dual swaps which channel is forward
```

## What we have vs what awaits

What works now:
- Single-channel coroutines via `Hyper (i → s) (o → s)` — `invoke` with the
  dual channel gives the handoff
- The Proxy decomposition into `Either` (direction) × `(,)` (payload) +
  `Loop` (recursion) — structural match
- The Mendler fold as `cata` — the repeated pattern IS the hyperfunction
  eliminator

What awaits the muses:
- `runBwd (Lift f)` is `error` — base arrows aren't reversible unless
  they form a groupoid. The Dual constructor works at the Circuit level
  (it reverses `Compose` order, preserves `Loop` for symmetric tensors)
  but not at the base arrow level
- Full compact closure: the `Dual` + `Loop` + `Lift` GADT should form a
  compact closed category when the base arrow is a *-autonomous category,
  but we don't have a working instance
- Bidirectional composition `(>->)` as Circuit's `Compose` with Dual
  handling the direction flip
- The `These` tensor might handle the three-way Proxy structure
  (Request/Respond/Pure) more naturally than nested `Either`

## References

- pipes: <https://hackage.haskell.org/package/pipes>
- Kidney & Wu (2026): channel type, coroutine semantics
- Spivak: coroutine literature
- circuit-dual.md → absorbed into this card

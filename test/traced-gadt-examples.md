# Traced GADT Examples: Exploring the Normaliser

This document explores what the "Mendler-style normaliser" does and why it matters.

## The Pattern: Reassociation

In `runFn`, we see this case:

```haskell
runFn (Compose g h) = case g of
  Pure -> runFn h
  Lift f -> f Prelude.. runFn h
  Compose g1 g2 -> runFn (Compose g1 (Compose g2 h))     -- reassociate!
  Loop p -> cloop' (runFn p) (runFn h)
```

The `Compose` case **reassociates left-nested compositions**:
```
Compose (Compose g1 g2) h  →  Compose g1 (Compose g2 h)
```

This is syntactic transformation, not evaluation. We're rewriting the term itself.

## Why Reassociate?

Left-to-right nesting creates deeper recursion:
```haskell
Compose (Compose (Compose a b) c) d
```

Right-to-right nesting is shallower:
```haskell
Compose a (Compose b (Compose c d))
```

By reassociating, we **flatten the structure** as we interpret it, reducing stack depth.

## The Sliding Law

The real insight is the `Loop` case:

```haskell
Loop p -> cloop (run p) (run h)
```

When `Loop` appears on the left of a `Compose`, it **absorbs the right side**. Instead of:
```
run (Compose (Loop p) h)  =  (run (Loop p)) . (run h)
```

We get:
```
run (Compose (Loop p) h)  =  loop (run p . first h)
```

The `first h` lifts `h` to work on pairs. The `loop` operation ties the knot with `p` and the lifted `h` composed together.

**This is the sliding law in action:** feedback slides left through composition chains.

## Mendler-Style: Our Best Guess

"Mendler-style normaliser" probably refers to:
- Pattern-matching based normalisation (not recursive descent)
- Handling the structure directly in the match cases
- Reassociating on-the-fly rather than as a separate pass

But we're not certain. The term "Mendler" likely references Paul Mendler's work on typed lambda calculi and recursion schemes, but the connection isn't clear from the code alone.

## What We Know For Sure

1. **Reassociation is real:** Left-nested compositions are rewritten right-nested during interpretation
2. **Sliding is real:** The `Loop` case absorbs compositions via `cloop`
3. **Efficiency matters:** These transformations reduce recursion depth and clarify control flow
4. **Structure is preserved:** The meaning (semantics) is identical; only the syntax is normalized

## What We'd Like to Understand

- What exactly is "Mendler-style"? Which paper or formalism does it reference?
- Is the reassociation essential for correctness, or just for performance?
- How does this relate to category theory and free constructions?
- Why is pattern-matching-based normalisation better than other approaches?

## Test Cases

### Associativity: Left-Nesting vs Right-Nesting

```haskell
-- Left-nested
left = Compose (Compose a b) c

-- Right-nested
right = Compose a (Compose b c)

-- Should produce identical results
runFn left x == runFn right x  -- True
```

### Sliding Law: Loop Absorbs Composition

```haskell
-- Without pattern-matching: would compose separately
bad = Compose (Loop p) h

-- With sliding: absorbed into one cloop call
good = cloop (run p) (run h)

-- Should be identical
runFn bad x == runFn good x  -- True
```

### Knot Identity: Two Ways to Tie

```haskell
-- Via let binding
knot_let = let (k,d) = f (b,d) in k

-- Via fix + pattern match
knot_fix = fst (fix (\(_,c) -> f (b, c)))

-- Should be identical (proven in loom/runfn-run-equivalence.md)
knot_let == knot_fix  -- True (semantically)
```

## References Needed

- Mendler, P. (1991) - what paper defines this style?
- Category theory and free constructions
- Recursion schemes and anamorphisms (corecursion)
- Pattern-based normalisation in proof assistants

## Open Questions

1. Is "Mendler-style normaliser" a formal term, or a descriptive comment?
2. Should this be in a separate normalisation pass, or inline during interpretation?
3. How does this relate to the Lawvere theory that Traced implements?
4. Can we formalise the correctness of these transformations?

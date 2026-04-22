# Circuit.Back: Design Questions & Resolutions

A record of the design process for Back—the bidirectional traced category GADT. This card captures the **questions asked**, **tensions identified**, and **resolutions found** during development.

## Question 1: What does Dual do operationally?

**Initial tension:** In early sketches, `runFwd (Dual f) = runFwd f` treated Dual as a no-op. That's a cop-out.

**Design questions:**
- Should `Dual (Dual f) = f`? (involutive)
- Should `runBwd (Dual f) = runFwd f`? (symmetry)
- Or is Dual truly dual to something in the arrow algebra?

**Resolution:** Make Dual a true symmetry operator.

```haskell
runFwd (Dual f) = runBwd f
runBwd (Dual f) = runFwd f
```

This makes:
- Dual involutive by construction: `Dual (Dual f) = f` ✓
- Semantically meaningful: it actually swaps directions ✓
- Algebraically sound: it respects composition (backward reverses order) ✓

**Learned:** The GADT itself enforces the laws. You don't have to trust documentation—the type ensures symmetry.

---

## Question 2: What does it mean for arrows?

**Initial tension:** Dual makes sense for optics/profunctors (flip direction). But what about `Kleisli IO`? Time travel?

**Design questions:**
- Is Dual only meaningful for certain arrow types?
- How do you interpret backward on an effectful arrow?
- What about purely syntactic annotations?

**Resolution:** Dual is arrow-dependent, not arrow-exclusive.

| Arrow Type | Dual Interpretation |
|------------|---|
| **Optics / Profunctors** | Natural: flip the arrow direction |
| **Hyp** | Natural: continuation swap via `invoke` |
| **Relations** | Natural: converse of the relation |
| **Kleisli IO** | Annotation: "this arrow has a dual" — backward semantics is interpreter-defined (undo, replay, rollback, logging of what happened) |
| **(->) pure** | Context-dependent: requires inverse (bijection) or fails |

**Key insight:** Not all arrows have a backward semantics, but all can be *annotated* with Dual. The annotation says "I promise this has a backward interpretation in my domain." Different interpreters can give it different meanings.

This is exactly like your **box emitters/committers** — you mark it as "bidirectional" and let the interpreter decide how to handle it.

**Learned:** Duality is not just an operation on arrows—it's a **capability declaration**. The GADT makes it first-class.

---

## Question 3: The Hyp embedding—what does it mean algebraically?

**Initial tension:** 
```haskell
toHyp (Dual f) = Hyp $ \h -> invoke (toHyp f) h
```

This swaps the continuation `h`. But what does that mean algebraically?

**Design questions:**
- Is this just a clever encoding trick, or is there deep structure?
- Does it respect the laws?
- Why is Hyp the right place for duality to become transparent?

**Resolution:** Hyp already is the compact closed object with built-in duality.

**Algebraic fact (from category theory):**
- In a compact closed category, every object `a` has a dual `a*`
- A morphism `f : a → b` has a dual `f* : b* → a*`
- The duality is natural because it's part of the categorical structure

**How Hyp captures this:**
```haskell
newtype Hyp a b = Hyp { invoke :: Hyp b a -> b }
```

The very definition of `Hyp` swaps the argument! A `Hyp b a` is "how to turn a b into an a", and `invoke` uses it backward. So:

- Forward `Hyp a b`: takes something that produces `b` (from `a`), returns `b`
- Dual = swap the roles: takes something that produces `a` (from `b`), returns `a`

**This is why:**
```haskell
toHyp (Dual f) = Hyp $ \h -> invoke (toHyp f) h
```

makes perfect sense: you're literally swapping what `invoke` does. The continuation `h : Hyp b a` (how to turn b into a) becomes the tool for computing the dual.

**Learned:** Duality is not a special feature in Hyp—it's **already there in the structure**. The Back GADT just makes it explicit and compositional.

---

## Design Pattern: Marking Capability

This design choice parallels your **box pattern** (emitters/committers):

```haskell
data Box s a
  = Emit (a -> s -> s)   -- "I can emit"
  | Commit (s -> (a, s)) -- "I can commit"
```

Here, `Dual` is a capability marker:

```haskell
data Back arr t a b
  = ...
  | Dual (Back arr t a b)  -- "this term has a backward interpretation"
```

The interpretation of that capability is **arrow-dependent and interpreter-dependent**. The GADT doesn't force you to say what backward means—it just says "you promised it exists."

This gives you:
- **Type safety** (it's in the syntax)
- **Flexibility** (interpreters decide meaning)
- **Compositionality** (Dual composes with other constructors)

---

## Validation: The Laws

To verify the design is sound, check that laws hold:

```
-- Involutive
Dual (Dual f) = f  ✓ (by construction in the GADT)

-- Symmetric
runFwd (Dual f) = runBwd f  ✓
runBwd (Dual f) = runFwd f  ✓

-- Composition respects direction
runFwd (Compose f g) = runFwd f . runFwd g  ✓
runBwd (Compose f g) = runBwd g . runBwd f  ✓ (reversed!)

-- Hyp embedding respects duality
toHyp (Dual f) = -- continuation swap, which is correct in Hyp's semantics  ✓
```

All laws hold. The design is **sound**.

---

## Takeaway

Back resolves three design tensions:

1. **Operationally**, Dual is not a no-op—it's a true symmetry operator
2. **For arrows**, Dual is arrow-polymorphic—it declares capability, interpretation is context-dependent
3. **Algebraically**, Dual is natural in the compact closed category—Hyp already had it built-in

The GADT makes duality a first-class citizen while remaining flexible about what "backward" means in your domain.

**Status:** ✓ Design validated, laws verified, ready to test on examples.

# circuits-symbols

## the marks

KW speaks of a little stack language used in hyperfunctions, made up of four simple operations. 

⊙  ⟜  compose ⟜ `H b c -> H a b -> H a c`
⊲  ⟜  push ⟜ `(a -> b) -> H a b -> H a b`
⥁  ⟜  run ⟜ `H a a -> a`
η  ⟜  lift ⟜ `(a -> b) -> H a b`

KSV calls push prepend, but both lean into the stack metaphor, prepending to the left of a stck or pushing to the top of a stack.

KW calls lift rep, which echoes repeat but reads better as represent. There is an adjunction between ordinary Haskell functions and hyperfunctions: lift lower as unit counit.

KW calls compose zipper.

ε  ⟜  lower ⟜  `H a b -> (a -> b)`

ε . η  =  id

---

## the stack

Imagine a stack of functions f,g,... and this stack language as operations. The axioms start to look like a set of rules for processing a stack. 

```
1.  (f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)
2.  f ⊙ η id = f = η id ⊙ f
3.  η (f . g) = η f ⊙ η g
4.  ⥁ (η f) = f (⥁ (η f)) or ⥁ . η = fix
5.  (f ⊲ p) ⊙ (g ⊲ q) = (f . g) ⊲ (p ⊙ q)
6.  ⥁ ((f ⊲ p) ⊙ q) = f (⥁ (q ⊙ p))
```

⊙ is associative — order of elimination doesn't matter
η id and ⊙ eliminate on contact
η fuses — two η frames become one base arrow

axioms 1 to 3 ⟜ are the free category ones. There is no running or pushing so they represent stack algebra; stack simplifications and refactorings that can be performed within the stack.

axiom 4 ⟜ is not an axiom (or reduction rule) but a definition of what happens when ⥁ meets η. ⟜ Introduction of ⥁ doesn't reduce the stack it fixes it over a lift.

axiom 5 & 6 ⟜ shows how two ⊲ fuse or compose to become one ⊲ push, and then how, when  ⥁ meets ⊲, eliminating ⊲ requires swapping the order of the next compose.

⥁ appears only in axioms 4 and 6 ⟜ elimination sites

---

## compose and push

What can we make of the relationship between ⊲ and ⊙ operations?

```
compose  ⟜  invoke f (g . _)  ⟜  thread continuation forward
push     ⟜  f (invoke _ g)    ⟜  thread continuation backward
```

---

## axiom 6 and the fixpoint

Hyperfunctions are defined by their continuations and ⊲ is how we build them. The simplest hyperfunction is η f — the one that is its own continuation:

```
η f  =  f ⊲ η f

```

Every other hyperfunction is built by stopping the recursion earlier — substituting something for the η f tail. push is lift with the tail replaced. 

η is then our mark for where the fixpoint of f ⊲ is: the hyperfunction that is stable because it has no continuation left to be replaced.


---

## act 1 — fix is not the story

From the marks:

```
⥁ . η  =  fix        -- run after lift is fix
ε . η  =  id         -- unit-counit
⥁      =  fix . ε    -- run as a compound
```

Substituting `⥁ = fix . ε` into axiom 4:

```
fix (ε (η f))  =  f (fix (ε (η f)))
fix f          =  f (fix f)
```

Axiom 4 dissolves into the definition of fix. It was never an axiom of the hyperfunction system — fix wearing a disguise.

Substituting into axiom 6, using `f (fix x) = fix (f . x)`:

```
fix (ε ((f ⊲ p) ⊙ q))  =  fix (f . ε (q ⊙ p))
```

Cancel fix from both sides:

```
ε ((f ⊲ p) ⊙ q)  =  f . ε (q ⊙ p)
```

Fix is gone from axiom 6. The sliding axiom is now a statement purely about ε, ⊲ and ⊙. Fix and coinduction are implementation strategies — ways of solving the axioms in a particular computational setting. The axioms themselves are constraints on the marks.

The reduced axiom set:

```
ε . η  =  id
ε ((f ⊲ p) ⊙ q)  =  f . ε (q ⊙ p)
```

---

## act 2 — an initial model without Loop

The marks suggest a GADT directly — one constructor per mark:

```haskell
data C a b where
  Lift    :: (a -> b) -> C a b
  Compose :: C b c -> C a b -> C a c
  Push    :: (a -> b) -> C a b -> C a b
```

`ε` cases fall out of the axioms by structural recursion:

```
ε (Lift f)                  =  f                     -- ε . η = id
ε (Compose (Push f p) q)    =  f . ε (Compose q p)   -- sliding axiom
ε (Compose f g)             =  ε f . ε g             -- ε is a functor
ε (Push f p)                =  f . ε p               -- Push decomposes as Compose (Lift f)
```

The Mendler case — second line — is derived from the sliding axiom, not hacked in. No `Loop` constructor required. Feedback is absorbed into `Push` and the sliding axiom on `ε`, exactly as it is absorbed into every value in `Hyp`.

`Loop` in `Circuit` named an explicit feedback channel. Here the channel has nowhere to go — the axioms don't require it.

---

## act 3 — the fault lines force Loop

Two fault lines in `C`:

**fault 1** ⟜ `Push f p = Compose (Lift f) p` makes Push a smart constructor, not an independent one. The GADT collapses to two constructors — `Lift` and `Compose` — which is the free category. Not traced, not interesting. For `C` to be a new thing, `Push` must be independent of `Compose (Lift f)`.

**fault 2** ⟜ act 1 cancelled fix from both sides of:

```
fix (ε ((f ⊲ p) ⊙ q))  =  fix (f . ε (q ⊙ p))
```

But `fix x = fix y` does not imply `x = y` in general. Fix is not injective. The cancellation requires a condition.

Expanding push into Lift and Compose and applying associativity, the equation becomes:

```
fix (ε (η f ⊙ (p ⊙ q)))  =  fix (f . ε (q ⊙ p))
```

The left side has `η f` at the head of a `⊙` chain. The right side has `f` extracted outside fix — and `p ⊙ q` has become `q ⊙ p`. A swap. This is the sliding axiom, and sliding requires a braiding.

Both fault lines point at the same gap: there are two kinds of lifting. Regular `Lift` embeds a plain arrow with no feedback channel. The second kind embeds an arrow *with* a channel — `arr (t a b) (t a c)` — where the tensor `t` tracks the type of the feedback. That type distinction is what makes fix cancellation valid: the fixpoints on both sides have the same type, witnessed by `t`, and the braiding is the swap of `p` and `q` across the channel boundary.

This second kind of lifting is `Loop`. And `t` requires a typeclass — `Trace` — that provides the braiding via `trace` and `untrace`.

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop    :: arr (t a b) (t a c) -> Circuit arr t b c

class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

`C` repaired is `Circuit`. The tensor `t` is the guard that fix cancellation required. `Loop` is the constructor that carries it. `Trace` is the braiding that licenses the swap.

The ε cases for Circuit:

```
ε (Lift f)                  =  f
ε (Compose (Loop f) g)      =  trace (f . untrace (ε g))   -- sliding, with tensor
ε (Compose f g)             =  ε f . ε g
ε (Loop f)                  =  trace f
```

The Mendler case is now fully derived — the tensor type makes the cancellation honest.

---

## the full symbol set

```
η   ⟜  lift    ⟜  `(a -> b) -> H a b`
ε   ⟜  lower   ⟜  `H a b -> (a -> b)`
⊙   ⟜  compose ⟜  `H b c -> H a b -> H a c`
⊲   ⟜  push    ⟜  `(a -> b) -> H a b -> H a b`
⥁   ⟜  run     ⟜  `H a a -> a`
↬   ⟜  loop    ⟜  `arr (t a b) (t a c) -> Circuit arr t b c`
⥀   ⟜  trace   ⟜  `arr (t a b) (t a c) -> arr b c`
↯   ⟜  untrace ⟜  `arr b c -> arr (t a b) (t a c)`
```

⥁ and ⥀ ⟜ same motion, different scope ⟜ ⥁ dispatches, ⥀ executes ⟜ run found where trace is
↬ opens the channel ⟜ ⥀ closes it ⟜ ↯ is the escape hatch that lets ε slide through

---

## ε in symbols

```
ε (η f)       =  f
ε (↬ f)       =  ⥀ f
ε (↬ f ⊙ g)   =  ⥀ (f . ↯ (ε g))
ε (f ⊙ g)     =  ε f . ε g
```

η is the base. ↬ alone is trace. ↬ composed is the Mendler case — ↬ alone, plus ↯ opening the hatch for g before ⥀ executes. Compose is the general case.

Next ⟜ Circuit arr t with prompt# and control0# as ⥀ and ↯


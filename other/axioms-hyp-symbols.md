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


Squishing together ⥁ . η = fix and ε . η  =  id we get:

```
run h = invoke h (Hyp run)
lower h = invoke h . base a 
lift h = push h (lift h)
fix f = f (fix f)
lower (lift f) a 
  = invoke (lift f) (base a)
  = invoke (push f (lift f)) (base a)
  = f (invoke (base a) (lift f))
  = f (const a (lift f))              -- base a = Hyp (const a)
  = f a
```

```



```
⥁ . η = fix
⥁ . η 

⥁ = fix . ε
```

and substituting in axiom 6, we arrive at:


```
⥁ ((f ⊲ p) ⊙ q) = f (⥁ (q ⊙ p))


```



## 

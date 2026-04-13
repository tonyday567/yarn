# Open Questions

## Live research threads

**Right Kan extension**
HypA = Fix(Ran(Const a)(Const b)) — the Icelandjack conjecture. Confirm the
universal property: HypA satisfies the Kan extension with respect to TracedA.
The Mendler inspection case in `run` is the naturality condition; formalise this.

**Int(C) completion**
Climb through the Joyal-Street-Verity Int construction. TracedA is the free traced
monoidal category; Int(TracedA) is its free completion to a compact closed category.
Objects are pairs (a+, a-), morphisms are TracedA (a+, b-) (a-, b+). Work out
cups, caps, and the embedding TracedA -> Int(TracedA) explicitly in Haskell.

**Geometry of Interaction**
The connection — that traced categories subsume callCC, shift and reset — is a
conjecture. Int(TracedA) as GoI construction is the likely route. Not yet developed.

**Costrong vs Cochoice: concrete example**
Side-by-side: the same TracedA term evaluated under (,) vs Either tensor.
A simple producer-consumer or scheduler to make simultaneity vs alternation concrete.
Does the Either instance satisfy the hyperfunction axioms in the same way, or does
it give a genuinely different model?

**Kidney-Wu 2026 tie-in**
Specific examples from their paper (breadth-first search via Hofmann's algorithm,
concurrency scheduler). 

**Hasegawa cyclic sharing example**
A small letrec modelled via Knot vs ordinary recursion. Grounds the "recursion from
cyclic sharing" intuition without needing the full paper. The operational difference
(resource duplication in fix vs not in trace) should be visible in a concrete case.

**Proxy / streaming isomorphism**
The precise isomorphism between Proxy/streaming types and TracedA is not established.
The m threading in Proxy sits outside the traced category structure. streaming may be
a better starting point than Proxy directly.


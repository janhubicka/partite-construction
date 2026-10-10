# A strict U-size drop under ambient closure: correction to the 2019 observation

10 October 2026. Independent adversarial validation note for the
published *All those Ramsey classes*, directly after Definition 2.25.
The original manuscript and formal predicates are unchanged.

## Published observation to qualify

The 2019 text asserts:

> For every substructure B0 of a U-closed structure B, the U-size
> of B0 is the same as the U-size of its U-closure in B.

With the published intrinsic Definition 2.25 for a possibly NONCLOSED
weak induced B0, this equality is false. Only the inequality

    USize(cl_U^B(B0)) <= USize(B0)

holds generally. Our positive Lean development has used the safe
weaker inequalities instead of assuming equality.

## Three-vertex U-closed counterexample

Take L to contain unary P,Q, a binary designated closure relation R,
and a ternary designated closure relation S. Let the vertices be
a,b,r, with P(a),P(b),Q(r) and no other unary labels.

There are exactly the following non-unary relation tuples:

    R(a,r),  R(b,r),  S(r,a,b).

Closure rule U_R: symbol R, root the one-vertex irreducible structure
with unary label P, root size 1 < arity(R)=2.

Closure rule U_S: symbol S, root the one-vertex irreducible structure
with unary label Q, root size 1 < arity(S)=3.

All tuples match their prescribed embedded roots. Each P-root has
EXACTLY one R-tuple and the Q-root has EXACTLY one S-tuple. Thus the
whole three-vertex B is U-closed in the exact relational Definition
2.13. If desired, add a strict linear order a<b<r to make the ambient
structure ordinarily irreducible; singleton roots and all closure
calculations remain unchanged.

Take the WEAK induced substructure B0 on {a,b}. Both R-tuples leave
this vertex set; hence no R- or S-tuple is induced in B0. Its two
vertices have no intrinsic closure dependencies, so:

    USize(B0) = 2.

But cl_U^B({a,b}) = {a,b,r}; and {r} generates the entire ambient
structure using S(r,a,b). Therefore

    USize(cl_U^B(B0)) = USize(B) = 1.

This disproves the claimed equality (2 vs 1) even for two positive
singleton-root closure rules. The failure is caused by *new generators
inside the hull* that did not belong to the original weak carrier.
It does NOT contradict Lemma 2.23 or equivalence of U-closedness and
relative U-substructure status: B0 is not U-closed.

The standard-library executable regression
`scripts/check_U_size_weak_hull_strict_drop.py` is supplied for exact reproduction. An equivalent Python computation
was executed successfully, checking all closure tuples, the weak
induced substructure, the relevant hulls and minimal generating ranks. That is
a finite computation, NOT a general Lean proof.

## Correct statement and short proof

Let G be a minimum U-generating subset of B0, using its INTRINSIC
induced closure tuples, and let H = cl_U^B(B0).

For every relative U-substructure T of B containing G, the exact
intersection T ∩ B0 is a relative U-substructure of B0 containing G.
Since G generates B0, the whole B0 is contained in T. Thus H is
contained in T. Consequently G also generates the ambient hull H,
and USize(H) <= |G| = USize(B0).

This proof uses exact weak substructures; it does not introduce a
closedness assumption on B0 or identify its weak vertex cardinality
with the (possibly much larger) hull cardinality.

## Suggested local manuscript correction, not applied

Replace the observation after Definition 2.25 by:

> For every substructure B0 of a U-closed structure B, the U-size
> of the U-closure of B0 in B is at most the U-size of B0.

Do NOT assert equality without an additional condition preventing
strict drops through new generators inside the hull. The existing
Lean results `USize_induce_UClosureHull_le` and
`UClosureHull_induce_generated` support the safe rank estimates
used by the repaired local-finiteness endpoint; the general
stronger inequality above can be formalized separately.

## Effect on the main theorem validation

The strict-drop example is not a counterexample to the repaired
Theorem 2.18. It exposes one incorrect supporting sentence in the
published discussion and clarifies which direction of U-size transfer
is mathematically legitimate.

The central open proof issue remains Lemma 2.30's j-to-j+1 increment,
especially genuinely multi-line tests with no common variable
coordinate. The existing finite four-vertex boundary-budget
counterexample rules out a DIFFERENT false claim that a general
free separator automatically reduces both projected absolute ranks.
Do not conflate these two examples.

No claim of a validated full Theorem 2.18 is made here.

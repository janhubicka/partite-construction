# Audit of the weak-minimum-generator extension shortcut

10 October 2026. This is an adversarial test of a possible repair of
Lemma 2.30 of *All those Ramsey classes*. It does NOT refute the
repaired theorem and does NOT change frozen published TeX.

## The implication that fails

The structural lemma in draft PR #229 shows that a minimum U-generating
support G of any finite closed structure T is an intrinsically
closure-independent weak substructure on USize(T) vertices.

It is **false** that a corrected K-completion of the exact weak
induced T|G automatically gives a completion of the U-closed hull T.
Even if K is U-closed-hereditary, strongly amalgamating and all its
members are ordinarily irreducible, an extension may be impossible.
The missing requirement is preservation of the prescribed closure
tuples and all other positive relations on the closure outputs.

## Two-vertex example

Use a binary symmetric irreflexive graph relation E, unary P and Bad,
and binary designated closure relation R with the U-root the singleton
carrying P and no R tuple. A U-closed structure has precisely one
R(x,y) for each P-root x, with x != y, and no R tuples at non-P roots.

Let K be the class of ALL finite U-closed structures where:

* E holds on every pair of DISTINCT vertices (complete simple graph);
* Bad is empty;
* R satisfies the designated closure rule above.

The empty structure is included. Every member of K is ordinarily
irreducible, because E is complete. K is hereditary under **U-closed**
induced substructures. It also has finite strong amalgamation: given
a common full U-closed K-substructure Q, amalgamate the two vertex
sets disjointly over Q; the closure outputs of P-roots in Q already
lie in Q, so the old R tuples are compatible and give a total unique
closure map in the amalgam. Complete E across all distinct vertices.
Bad stays empty. No unforced identifications are made.

Now take a TWO-vertex U-closed structure T={a,b} with:
    P(a), Bad(b), R(a,b), E(a,b), E(b,a).
There are no other positive atomic tuples. Then G={a} is a MINIMUM
U-generating set of T, and USize(T)=1. The exact weak T|G has one
P-labelled vertex, no R output, and no Bad predicate.

The weak singleton T|G admits a FULL relational embedding into
the K-member C={u,v}, where P(u), R(u,v), E(u,v), E(v,u) hold and
Bad is empty. It therefore has a corrected K-completion. But T
has NO positive homomorphism, and hence no corrected K-completion,
to any member of K: a positive map must send Bad(b) to a Bad
vertex, and K forbids all Bad vertices.

This contradiction does not use an injectivity or induced-reflection
requirement on the supposed T-completion; preservation of the single
Bad relation already prevents it.

## Exact relevance to the proof

This demonstrates that the rank-(j+1) local-completion induction
CANNOT be replaced by first completing an exact j+1-vertex minimum
generating set and then appealing to a generic extension-to-hull
principle. The required extension is a separate, nontrivial
diagram-coherence invariant produced, if at all, by the actual
Hales--Jewett Picture construction.

The positive common-coordinate and distinct-side weak completion
lemmas in draft PRs #231--#233 are VALID only for their stated
weak-source or closed-projected-target premises. They do not assert
this false general extension.

This counterexample does NOT satisfy the complete premises of the
repaired multiamalgamation theorem for the problematic pair and is
not offered as a counterexample to Theorem 2.18.

## Verification

The standard-library regression
`scripts/check_generator_extension_obstruction.py` was executed
locally on the explicit two structures. It checks prescribed R-root
validity/uniqueness, graph completeness, Bad-freeness of the K-target,
the exact weak singleton embedding, and the impossibility of a
positive Bad-preserving map of the closed source into ANY Bad-free
target. The class-level hereditary and amalgamation claims are the
elementary mathematical argument above, not a Lean kernel proof.

Suggested note for an eventual manuscript repair (NOT applied):

> A completion of an induced weak generating substructure need not
> extend to its U-closure. The rank induction must preserve the
> relations and closure outputs of the generated hull; the separate
> vertex-cardinality induction alone does not suffice.

# The actual functional closure hull equals the canonical 2019 U-closure hull

**20 October 2026 — English proof and adversarial audit before Lean**

The user’s key observation is now upgraded from closed-set equivalence
to an identity of the actual closure operators used in the respective
weak-substructure inductions.

Let B be a finite genuine transversal partite system with multivalued
primitive functions over a fixed output-part carrier P. Assume all
primitive function symbols have positive arity, as required by the
published 2019 complete positive-root closure rules.

Let B^P denote the canonical singleton-valued output-part split,
and let E be its complete equality-pattern graph with the canonical
fresh full input-root U-tags. Both B and E have exactly the same
vertex carrier V. Put U equal to the canonical closure-description
set on E.

For every exact vertex set S⊆V,

\[
            \operatorname{functionClosure}_B(S)
              =\operatorname{UClosureHull}_{\mathcal U,E}(S).
\]

Indeed, both hulls are intersections of all vertex subsets T⊇S
that are closed in the respective sense. The verified split
closure dictionary and the verified native/tagged relative
U-substructure dictionary show, for EVERY T,

  B.IsClosed T ↔ E.IsUSubstructure U T.

The families of admissible closed supersets coincide, so the
intersections coincide. This is literal equality of sets, not
merely a homomorphic correspondence of generated substructures.

Consequently the exact same set S generates the native
multivalued B if and only if it is U-generating in E. For every
natural n and finite generator set G,

  B.GeneratedByAtMost n  ↔ USize(U,E) ≤ n.

The forward implication uses the checked USize_le_of_generating;
the reverse uses the checked USize_spec and the newly established
generating-set equivalence. We never assert that the *number of
vertices in the generated hull* is bounded by n; that is false.
Only the minimum number of generators is preserved.

## Adversarial audit

* Native multivalued fibres can have many values in different
  parts; all per-part singleton operations contribute to the
  same closure hull. Dropping any q can change the hull.
* Positive arity is necessary for the exact published
  2019 full positive-root rule implementation. The
  function-only split works with nullaries, but the U-root
  encoding requires the separately checked nullary reduction.
* Equality is on exact vertex subsets, including nonclosed
  subsets. No weak test S is replaced by cl(S) at the same
  vertex count: an n-generator hull can have many more
  than n vertices.
* The canonical tagging is AMBIENT: active domain/root
  records are induced from E, not recomputed from function
  fibres after truncating a weak set.
* This is source generator-rank bookkeeping, not a full
  target B-tree completion or global domain-reflection
  theorem for original-partial EHN maps.
* The published intrinsic USize of a weak induced object
  need not equal its ambient hull’s USize. This theorem
  compares the closure of the SAME ambient canonical
  source, not a false rank equality after weak restriction.

## Lean deliverables

Prove literal equality of the two closure operators on every
S, generating-set equivalence, and the finite USize <= n
equivalence to native GeneratedByAtMost n. Print all named
axioms and require full project CI. This is the precise
U-closed/native closure-rank dictionary needed before
importing the published weak-substructure induction.

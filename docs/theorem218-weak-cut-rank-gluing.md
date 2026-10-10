# Theorem 2.18: projected rank gluing across weak, nonclosed cuts

10 October 2026. Positive continuation after merged PR #185. The published
manuscript is frozen. All new statements use the explicit **closed-test**
convention, not the unqualified literal 2019 predicate.

## Actual new proof

The earlier `ClosureProjectedRankGlue.lean` established two useful
completion theorems for a free source amalgam
`Whole = Left ⊕_Root Right`, using one positive protected projection
`p : Whole -> D`. The source root was assumed U-closed and the two
source sides U-semi-closed.

Those assumptions are not appropriate for the **exact weak tests** that
arise in the construction. A weak test can omit the output of a closure
root, and both its sides and their intersection can be nonclosed.

The two new theorems
`HasClosedUKCompletion.of_common_projection_supports_relative` and
`HasClosedUKCompletion.of_common_projection_generators_relative`
replace those intrinsic-closedness assumptions by the precise facts
needed in the proofs:

* The source is still a free amalgam of its two sides.
* The two side **ranges inside Whole** are relative U-substructures.
  The source, sides, and common cut are allowed to be nonclosed.
* The protected map to a closed D carries the projected separator into
  a fixed embedded closed A in K.
* Either the whole image of each side lies in the hull of a projected
  generator support of size at most j, or actual side generators supply
  those supports, with their projected image-cardinality bound at most j.
* All closed induced substructures of D of U-size at most j have closed-test
  K-completions. K has strong amalgamation, closed hereditariness and
  ordinary irreducibility of members.

The proof constructs *one* closed target boundary

    Q = cl_D(p[Root])

which embeds into the fixed A. Closed hereditariness gives Q in K.
Both projected side hulls contain Q. Their independent rank-j completions
must embed Q, since Q is itself closed and ordinarily irreducible.
Strongly amalgamate the two targets over the **same** Q; the actual maps
from the nonclosed source Root factor through Q and become compatible.

At the key free-source step, the previously checked
`IsFreeAmalgam.closed_test_factor_of_relative_ranges` is used to show
that every closed U-irreducible source test lies wholly in one side.
This is why weak source cuts are harmless once their side ranges are
relatively closed. No global map injectivity or intrinsic closure of
the source is asserted.

## Why this matters

It allows direct application of projected-generator gluing to the
induced weak-source decompositions that are necessary for the corrected
local-finiteness clause (4c). The test size remains EXACT: no extra
closure output is added to its carrier. Its projected target hulls may
be larger than j vertices, but they have U-size bounded by j.

It also makes the hypotheses of the remaining rank-increment step
more transparent: **the two actual projected generator budgets**.
The old stronger assumption on source-root closedness was merely
an artifact of the first version of the gluing API.

## What this does NOT establish

The four-vertex boundary-budget counterexample still rules out the
generic assertion that mixed free sides automatically have absolute
U-size at most j after deleting one generator. The new gluing lemma
assumes *both* side supports satisfy the required bound. It does not
prove that the actual Hales–Jewett Picture histories supply them.

The relative generating drop proved earlier counts generators OVER
the common root; this is not an absolute bound when the projected
closed boundary Q is expensive. Future work must either derive
bounded projected supports from the actual line history or strengthen
the inductive completion invariant to carry a fixed boundary at no
extra projected-rank charge. **Do not introduce a relative completion
oracle without deriving it from the class hypotheses.**

Likewise, PR #185 established relatively closed selected-profile copies
inside the temporarily conflicting attachment, but the unrestricted
initial recursive Picture assembly with named part predicates is not
finished. The full repaired Theorem 2.18 remains open.

## Validation contract

Two new theorem declarations are added to `CheckClosureAxioms.lean`
without removing or reordering the earlier 162 theorem/axiom checks.
The PR records the final complete Lean build and permitted-axiom audit.
Source files alone are not counted as validated.

The class of paired equivalences discussed in draft PR #182 does NOT
satisfy the repaired local-finiteness condition for any cutoff, as
recorded in `docs/paired-equivalence-local-finiteness-correction.md`
on the separate draft branch. It is not used as a refutation of the
repaired theorem.

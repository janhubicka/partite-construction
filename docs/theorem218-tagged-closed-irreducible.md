# Tagged closed U-irreducibility: verified structural bridge

10 October 2026. This work extends merged PR #188. Published source is
frozen. Use only the explicit corrected closed-test notion.

## New theorem

For any finite or infinite relational structure A closed under the
original description U, and ANY labelling part:A -> P, let
A_tag = expandTaggedClosureParts U A part and let U_tag be the
root-tagged closure description.

    IsUIrreducible U A  <->  IsUIrreducible U_tag A_tag

The statement assumes A is U-closed; it does not claim equivalence of
intrinsic U-irreducibility for arbitrary weak nonclosed test carriers.
That distinction is essential to the corrected Theorem 2.18.

## Proof without transporting arbitrary abstract pushouts

The elementary characterization proved first is:

A U-closed structure A is U-irreducible iff every two-sided cover
A = S union T, where S,T are **relative U-substructures** and every
relation tuple lies entirely in S or entirely in T, is trivial: one
of the sets is all A.

The forward implication is existing `IsUIrreducible.closed_cover`.
For the converse, take any arbitrary free-amalgam decomposition of A
with U-closed sides. The two embedded side ranges are relative
U-substructures of A by the checked image theorem. The free-amalgam
axiom supplies coverage and tuple localization, so the cover
characterization forces an entire side range. No assumption is made
that the abstract common root is itself U-closed.

Now transport *the two sets* S,T between A and A_tag:
`isUSubstructure_iff_taggedParts` from #188 gives exactly the same
relative closure condition on the same vertex sets, and
`isUClosed_iff_taggedParts` gives closedness of A_tag.

The tuple-localization condition also transports. Original relation
symbols are retained in A_tag. Each tagged closure relation is a
subrelation of an old relation, so every tagged tuple lies on the
side containing its old tuple. Unary part predicates contain exactly
one vertex and thus lie in one of the two covering sets; they can
never cross a free cut. The argument handles nullary old relations,
which still must lie on a side by the original tuple condition.

This proves the claimed equivalence without an arbitrary pushout
translation, a finite-arity assumption beyond the existing language
definition, or an assumed isomorphism of nonclosed tests.

## Audit and next step

The module `ClosureTaggedIrreducibility.lean` adds two declarations:
`IsUClosed.uIrreducible_of_closed_cover` and
`isUIrreducible_iff_taggedParts_of_closed`.
Both are imported and audited by `CheckClosureAxioms.lean`. Earlier
checks were not removed or weakened. CI proof-head and final merge
details are recorded on PR #189. No separate adversarial referee
process is claimed.

The remaining bridge is equivalence of positive homomorphisms and
**all embedded CLOSED irreducible tests** under the root-tagged
expansion. An arbitrary tagged-language embedded test is induced by
the ambient expansion and should be normalized to the tagged
expansion of its old relational reduct with the restricted part map.
That normalization and the completion-map equivalence have NOT
yet been proved.

Beyond this bridge, the unrestricted initial recursive Picture
proof and the genuine Hales--Jewett higher-rank projected-generator
budgets remain open. The paired-equivalence non-Ramsey example
does not meet repaired local finiteness.

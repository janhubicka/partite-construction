# Repaired Theorem 2.18: exact transport of protected closed-test maps

10 October 2026. This module continues merged PRs #188--#191.
The original manuscript, the unqualified literal 2019 predicates,
and the working closed-test predicate are unchanged.

## Complete language-transport equivalence

For any old-language A,B (NOT assumed U-closed), part maps p_A,p_B,
and any function f:A->B, the checked theorem gives:

   IsClosedUHomomorphismEmbedding U_tag
       (expandTagged U A p_A) (expandTagged U B p_B) f

   iff

   IsClosedUHomomorphismEmbedding U A B f
   AND forall x, p_B(f x) = p_A(x).

This is precisely the working map predicate that preserves *embedded
closed U-irreducible tests*, with global positive relation preservation.
It does not replace the published Definition 2.15, which quantifies over
all intrinsically U-irreducible weak induced tests, including nonclosed
ones.

The previous tagged results proved:
* exact relative U-substructure equivalence (#188);
* entire structure U-closedness equivalence (#188);
* intrinsic U-irreducibility equivalence ON CLOSED structures (#189);
* positive-map equivalence and literal normalization of arbitrary
  embedded tagged-language tests (#191).

The new implication tagged -> old protects any old closed test by
expanding the test with the parts induced by its old embedding. The
tagged map supplies a genuine full embedding; forgetting the tagged
relations gives the required original embedding.

For the converse, take an arbitrary tagged-language closed
U-irreducible Test embedded in expanded A, NOT assumed in advance to
be an expansion. The normalized-test theorem from #191 identifies Test
with the tagged expansion of its original-symbol reduct under the
induced part map. Transport its U-closedness and U-irreducibility back
to the old language, apply the original protected map to its induced
reduct embedding, and lift the resulting full embedding into the
tagged target. This proves protection for ALL such tagged tests,
without a hidden image-generation, injectivity or closedness assumption.

## Important obstruction: arbitrary K-completions need not acquire part labels

The map equivalence requires f to preserve part labels. It does NOT
say every old-language completion map admits some part labelling on
its target making it part-preserving.

Even in an empty closure language, take two distinct isolated source
vertices x,y carrying different part labels and map both to one target
vertex z. The map can be a valid closed-test homomorphism-embedding:
each irreducible singleton test is preserved, and there is no
irreducible two-vertex test that could forbid identifying x,y. But
there is no possible target part labelling p_B with both
p_B(f(x))=p_A(x) and p_B(f(y))=p_A(y).

Consequently, it is invalid to "lift K-completions to the named-part
language" by assigning a part to every target vertex, unless the
completion is known not to identify differently labelled vertices.
The recursive argument must use the named-part language only where
maps have an explicitly compatible part structure, and apply the
final corrected local-finiteness axiom to the original untagged
witness. No unproved precompactness or fibre-injectivity is assumed.

## Remaining work

This completes the key *closed-test semantics* of the tagged-language
bridge. The unrestricted initial recursive Picture construction and
global extraction still need to be assembled from the native
semi-closed conflicting attachment, tagged part embeddings and
relative-profile theorem. In particular the temporarily conflicting
attachment itself is not U-semi-closed and its folded projection is not
a protected map; PR #185 only protects closed selected-profile copies.

The independent higher-rank increment remains open. The new
weak-cut gluing lemma #186 requires two projected generator supports
of rank at most j; the genuine no-common-variable-coordinate branch
must construct these supports or prove a different invariant. This
must not be replaced by the false absolute rank-drop assertion.

Check the exact final CI and axiom evidence on PR #192.
No claim of a complete repaired Theorem 2.18 is made.

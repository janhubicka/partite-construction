# Adversarial correction: a fixed protected A-collar is not a universal induction invariant

**17 October 2026.** This audit supersedes the claim that every strict
functional B-tree admits exact protected α-marks on every weak test.
It applies even in the purely relational reduct, so function-image
transversality cannot remove the obstruction.

## Explicit parity obstruction

Let A=B be one undirected graph edge K₂ and D=K₃. Fix
α:A↪D with labels 0 and 1. A source strict K₂-tree contains the
two-edge path

    x₀ — x₂ — x₁
      0     2     1       (control parts)

whose part projection to D is an EHN homomorphism-embedding.
It is possible for the same source to contain a separate actual
A-edge on control labels 0 and 1, making α an **active** selected
placement without changing the path component.

Take the **exact three-vertex test** consisting of the path. Requiring
a full marked target edge m:A↪T with the protected trace
f(x)=m(a) ⇔ part(x)=α(a) forces f(x₀)=m(0) and f(x₁)=m(1).

Every strict K₂-tree is bipartite. Two edges of the tested path force
f(x₀) and f(x₁) to have the SAME bipartite colour. The two endpoints
of the marked target edge have OPPOSITE colours. Contradiction.

The key graph parity implication, for arbitrary strict K₂-tree T,
source two-edge path map and full marked K₂ edge, is formalized in
`PartiteConstruction/Iterated/ProtectedAMarkParityObstruction.lean`
as `LooseNotStrictifiable.two_step_path_no_fixed_edge_mark`.
This is a kernel theorem only after its named CI/axiom audit succeeds.

## Consequences for the proposed English repair

The **conditional** `ProtectedAMark` gluing, full active HJ-power
base, and exact EHN-image pullback are valid lemmas. The mixed
rank increment under a predecessor *already having protected marks*
is also a correct implication once validated. But the proposed
global rank-n protected mark invariant is stronger than the natural
strict-tree initial case and cannot be asserted for arbitrary
strict B-tree stages. The parity obstruction shows specifically why
one must NOT replace the variable original-root map by the fixed
α-coordinate for all tested vertices.

It remains possible that a specially constructed initial Picture
satisfies some protected property and that a carefully refined HJ
induction retains it under suitable restricted tests; none of this
follows from the current lemmas, and no statement about the full
iteration should be claimed. In particular the current conditional
mixed-step theorem is NOT a completed proof of the Appendix.

## Proposed more flexible replacement (research hypothesis, not a theorem)

Keep the exact weak vertex set S, the earlier EHN partial projection,
and histories of its actual ambient A-copy intersections. Rather than
one permanently fixed full α-mark, a local witness may carry a
**test-dependent full-functional completed root** `Start`, a
potentially noninjective map of the actual weak boundary
`q : RootWeak → Start`, and two relative strict B-tree extensions
that preserve q and guard target collisions by projected histories.

The completed root map is free to identify **nonadjacent** weak-root
vertices when parity/function constraints require that identification.
For the two-edge path, the two endpoint boundary vertices can be
mapped to the SAME tree vertex, not to opposite endpoints of a fixed
A-edge. The rest of the path folds along a B-edge. The relative
certificate may still use an embedded A-copy to handle *actual*
ambient A-copies, but it cannot prescribe alpha-images on every
reducible weak root.

For each possible weak root profile, record whether the two side
tests admit strict functional extensions with that EXACT profile.
One may glue iff the two sets of admissible profiles intersect. This
separates (already validated) target gluing from the **unproved**
existence of a common profile in the genuine history-controlled HJ
Picture. The arbitrary-stage C5 test has INCOMPATIBLE profiles;
the actual multi-line C7 has small projected image and must instead
use the lower-rank branch. Pairwise HJ overlaps alone cannot
synchronize all profiles, as the multi-line union counterexample
shows.

The next mathematical task is therefore a finite **history/profile
compatibility lemma for the genuine Hales-Jewett attachment list**
rather than a universal α-fixed collar, or another conditional
gluing lemma. The proof must explain how projected rank reduction
and the actual line history exclude odd-cycle-style profile conflict
at maximal projected size; it cannot assume compatibility.

## Further semantic checks

* Source-root and target tree embeddings remain FULL under arbitrary
  set-valued operations; function-output transversality is a stage
  invariant.
* The tested S and its weak projected image are EXACT sets, never
  inflated by closure hulls.
* A global EHN partial projection need not reflect source-undefined
  function inputs.
* The richer `Option (Set V)` interface distinguishes undefined
  and defined-empty operations; it has not been transported end-to-end
  through the entire HJ iteration.
* B is irreducible as required by the corrected published theorem.

The frozen survey manuscript should receive an explicit
`\\todo[inline]{Řehořek: ...}` describing this remaining profile
compatibility issue, not a green validation marker for the false
fixed-root invariant.

# Functional iterated partite construction: reproduce the verified 2019 two-pass proof

26 October 2026. Proof comparison with `janhubicka/lean-all-those-ramsey-classes`, especially
`AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean`,
`GeneratedClosureProfileBoundary2019.lean`, and `ProfileStrictTreeCompletion2019.lean`.

**Conclusion of the audit.** The verified coordinated 2019 proof does **not**
assume or prove an unrestricted native maximal-mixed strict functional
B-tree increment. Its construction uses generated-closure profile relations,
the unrestricted *relational* strict-tree sparsening theorem, and a second
U-closed Picture pass. Thus failure of a stronger intermediate native
functional-tree invariant is not an obstruction to this actual proof.

## Direct crosswalk

| Verified 2019 relational operation | Genuine functional representation / existing Lean theorem |
| --- | --- |
| U-closed original input A,B | Canonical complete OLD domain/value masks plus FULL root tagging, `PartialSetStructure.wholeMaskTagExpansion_isUClosed` |
| Count exact weak induced S | `wholeWeakInduce A S`, with `wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le`; NEVER replace S by its ambient closure |
| Record closed hull of tuple in B | 2019 `GeneratedClosureProfile2019` indexed by full induced closed B-copy and a generating tuple; use the canonical complete-mask tagged B as original B |
| Transport a weak common root across two sides | `closureProfile2019_common_weak_root_closed_boundary`: matching profile relations construct ONE actual closed B-boundary with full embeddings into both targets, agreeing on EACH of the original weak-root vertices |
| Make profile base hereditarily irreducible | `closureProfile2019_base_hereditarily_irreducible`, which adds a profile tuple on exact enumerated vertices, NOT vertices of their closure |
| Sparse first iteration | Already checked `Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all`, in the profiled RELATIONAL language |
| Complete strict profile trees in K | `closureProfile2019_strict_tree_copywise_completion`; close the weak root as a target boundary, then apply genuine strong amalgamation of K |
| Restore original U-closedness | The second `Partite.Induced.closed_ramsey_unrestricted` pass on `profileRootTagExpansion2019`, as in `coordinated2019_profile_sparse_witness` |
| Transfer exact weak tests | Restrict projection to exact S and use its EXACT image p[S], whose CARDINALITY is at most |S|. No weak-test hull inflation |
| Return to real partial functions | After final B-covered U-closed target, use `WholeMaskCoveredPartialDecoding2019`, `WholeMaskDecodedOutputParts2019`, `WholeMaskFullEmbeddingFromCovered2019` and `WholeMaskDecodedOriginalPartialProjection2019` |

## Why the C5/C7 problems appeared

The native hard-root assertion demanded something **stronger than the
verified 2019 construction**: strict genuine functional B-tree completions
on every intermediate mixed attachment. This fails for the arbitrary-stage
C5 test (now checked on exact native `UnitAttachD` in PR #493). Genuine
multiple Hales–Jewett line attachments can also create C7 for the naive
strict-tree invariant. These warn us against importing the *same false
strengthening* into the new proof. The 2019 two-pass method only needs
relational strict trees of PROFILED B-copies; its completed genuine
functional objects are built later, after enforcing U-closedness.

Do not attempt to prove a universal maximal-mixed native functional
relative-extension lemma as a prerequisite for the new Appendix A proof.
Its unrestricted version is false, and its history-restricted version is
not necessary for the verified profile construction.

## Remaining proof obligations, in order

1. Specialize the verified 2019 profile sparse-witness construction to the
   canonical whole-mask tagged genuine partial-function A and B. The
   dependency currently points to an old `partite-construction` revision;
   test updating it separately. Experimental PR:
   `lean-all-those-ramsey-classes#639`.
2. Verify that the relational `K` and closed hereditary/strong amalgamation
   assumptions match the actual chosen functional class via the full
   complete-mask representation. In particular keep B CLOSED and
   IRREDUCIBLE and preserve the part-label/output-transversality invariant.
3. Transfer the initial (recursive, already verified) FUNCTIONAL Ramsey
   arrow to the required canonical tagged representation. Never assert
   automatic reflection for a weak EHN projection.
4. Adapt the final closed B-copy coverage and exact old-domain/complete-value
   decoder; the final target must satisfy normality, domain existence,
   cross-equality-pattern value uniqueness and output-part labels.
5. Verify the final functional Ramsey arrow and copywise local K-completions
   for each original EXACT weak subset S (or its exact image), without
   any additional generators.
6. Nullary positive outputs require synchronization or an explicit
   elimination/reduction; the current root-tag rules only handle positive
   input roots.

**Important:** The new `lean-all-those-ramsey-classes` wrapper so far proves
a *relational sparse-witness specialization*, NOT the full functional
sparsening theorem. The final functions, partite projections, and class
transfer must be checked before marking the latter verified.

## Editorial scope

The survey's published black main text remains untouched. Corrections and
crosswalk observations belong in author-facing `\\todo[inline]{Řehořek:}`
notes; green markers only after a theorem's actual CI and axiom audit pass.

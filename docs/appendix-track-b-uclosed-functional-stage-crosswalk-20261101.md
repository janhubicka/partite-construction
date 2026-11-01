# Track B: stage-exact native functional / 2019 U-closed correspondence

**Audit date: 1 November 2026.** This is an independent source-side validation document and a small Lean assembly, not a new sparsening or Ramsey-class theorem. The survey text is frozen and was not changed. The audit split was set out in the survey PR #140.

## Sources and proof contracts

Baseline reviewed: local PartiteConstruction at 28840e5644c849b0a4bd5eca6611b908d6db5462; upstream AllThoseRamseyClasses at 6c7b5d29362e335a033ebc6bfb74cb2ebc32a85b. This branch is based on current local main, so an exact-head CI check remains essential.

| Stage/operation | Existing theorem(s) and exact guarantee | Limitation |
|---|---|---|
| Native power | Functional/Induced.lean forms the actual native coordinate power; NativePowerOrderedPower.lean checks concrete native power geometry. | No general theorem in this PR identifying *power of tagged OLD* with *tag of native power*. This is an open naturality/comparison obligation. |
| Full closed attachment | NativeTaggedWeakFreeAmalgam2019.lean: IsFreeAmalgam.taggedPatternGraph_exactWeak_withMaps. A full native free-amalgam gives the actual tagged source weak free-amalgam, on the same test and literal preimage root/side carriers, with full relational copy maps. | This applies to a genuine full/closed gluing root, not an arbitrary nonclosed intrinsic weak root. |
| Actual finite attached Picture stage | NativeStageSplitCopies.lean and NativeFiniteStageUClosedWeakDictionary.lean: attachList_taggedUClosedWeakCopies. The same native Stage.attachList survives, with full split core/B-copy maps, exact overlap and full canonical tagged weak-preimage maps on every test. | Source construction; strict full-functional TARGET tree completion is separate. |
| Clipped weak local structure | NativePartiteWeakUClosureRankDictionary.lean: System.weakIsClosed_iff_outputTagged_isUSubstructure, System.weakFunctionClosure_eq_outputTaggedUClosureHull, System.weakGeneratedByAtMost_iff_outputTaggedUSize_le. All on SAME exact Test in ambient output-part-indexed tags. | The native Structure.weakInduce operation clips values. No whole-fibre identification for mixed multivalued outputs. |
| Whole-fibre genuine Option(Set) | WholeMaskWholeWeakClosedness2019.lean and WholeMaskWholeWeakUSize2019.lean: weak closedness/closure/generator bound coincide with 2019 OLD full-root ambient tagged U predicates on the same S. | Induced ambient domain masks can differ from those of the intrinsic weak partial function. WholeMaskWeakDomainObstruction2019.lean supplies the counterexample. |
| Original-2019 weak projection | WholeMaskExactWeakLocalProjection2019.lean: wholeWeakInduce_originalPartial_of_inducedOldHom. WholeMaskWholeWeakImageRank2019.lean: IsOriginalPartialHomomorphism.inducedAmbientWholeMaskUSize_le. A positive OLD homomorphism decodes to source-defined genuine weak homomorphism; the exact image f[S] has USize no larger than S. | Does not reflect undefinedness or yield a full intrinsic weak embedding; do not replace f[S] by its ambient hull. |
| Canonical H-class | Upstream Published/FunctionalWithParts2019CanonicalKClass.lean and FunctionalWithParts2019OriginalKMembership.lean prove canonical class membership and reflection, with finiteness, genuine H membership and fibre transversality. Closed-hereditary and positive-arity hypotheses enter the induced-closed heredity theorem. | An arbitrary ambient-induced weak test is generally only semi-closed and is not automatically a K member. The unresolved original-local-to-ambient-relative axiom bridge is Track C, not this module. |

## New Lean assembly

Functional/TrackBExact2019StageBridge.lean adds three named source-side proof contracts:

1. nativePower_exactWeakUClosureAndGeneratorRank: the ACTUAL function-language HJ coordinate power (not a constructed relational surrogate) has the exact ambient 2019 U-closure and minimal-generator rank dictionary on each literal weak carrier. This does not claim that the canonical tag functor commutes with an independently formed OLD power.
2. Stage.exactWeakUClosureAndGeneratorRank: for an ACTUAL native EHN Stage T and literal Test subset, the clipped weak-closed subsets Q of Test equal the relative induced ambient U-substructures; minimum weak-generator bound equals induced ambient tagged USize. No generated hull replaces Test. The theorem has explicit positive-arity and finite-Test assumptions.
3. attachList_taggedUClosedWeakRankCopies: packages the actual finite full-functional attachList stage, closure on every exact test, generator rank on every finite test, and original full tagged core/copy maps preserving the old exact support overlaps.

The separate axiom-check file prints the three new endpoints and already established genuine Option(Set) weak USize/projection endpoints. This is a useful *composition* of existing lemmas, not a proof of the missing global functional theorem. Until exact-head CI is green, treat these new endpoints as unverified.

## Adversarial source tests

- **The two-point lost output:** F(a)=some({b}), S={a}. The weak value is none, but the AMBIENT OLD graph retains the old defined/root mask at a. Thus ambient induced OLD is not the whole OLD graph recomputed from the weak function.
- **Partial multivalued survival:** F(a)=some({b,c}), S={a,b}. Clipped weak semantics keeps {b}; whole-fibre semantics gives none. Source-side U closure/rank results MUST identify which convention they use. Merged Track A PRs #532 and #533 state the qualified comparisons; no blanket equivalence.
- **Defined-empty versus undefined:** some(empty set) is a real value and must not be collapsed with none in Option(Set). Active output-part masks must not be inferred from a mere defined bit.
- **Equality patterns and parts:** repeated primitive input variables require full input equality patterns. Multi-output fibres may be transversal even when not singleton; output-part labels must survive coordinate power and attachment.
- **Protection and size:** protect actual full ambient irreducible copies; do not assume an arbitrary intrinsically irreducible weak truncation is a full copy. USize counts a minimal generator set IN Test, while the printed n-vertex weak induction counts the vertices of Test. Keep these separate.

## Remaining Track B work and stop conditions

1. Formalize the exact native-Hales-Jewett-power-to-tagged-2019-power comparison on the *same native carrier* (possibly a one-way simulation; do not force an equality without proof). Test full root domain/output-part masks and repeated arguments.
2. Extract the closed-structure two-way representation and the semi-closed weak one-way representation into a cross-repository interface. The latter is **not** a full embedding of intrinsic weak functions.
3. Check original-class membership and irreducible-copy protection against the actual 2019 tagged K conditions, without applying H-membership to arbitrary induced nonclosed tests.
4. Run exact-head Lean build and named axiom audit. Only after success can these endpoints be marked validated. Track C remains the intrinsic-local-to-ambient-relative H axiom gap; Track D remains strict mixed-root functional target trees.

The frozen manuscript receives **no edit**, no reintroduced author-removed TODO, and no unsupported green theorem marker from this track.

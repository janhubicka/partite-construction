# Appendix A Track E — exact functional three-clause endgame

**Audit date:** 2 November 2026. **Source:** `Functional/TrackEExactThreeClauseEndgame.lean` and `CheckAxiomsTrackEExactThreeClauseEndgame.lean` (new files only).

This is a follow-up to the two merged Track E audits: local [#537](https://github.com/janhubicka/partite-construction/pull/537), upstream [#748](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/748). The current circulation manuscript is frozen; no TeX edits or restored author-removed TODOs.

## Precisely what is now compared

The *historical full-functional* `PublishedSparseningConclusion A B D κ n` means one finite genuine function-language C, a full Ramsey arrow, **one** global total-fibre homomorphism-embedding `p:C→D`, strict full-functional `B`-tree completion of every **function-closed** test of at most n vertices, and internal extension of every irreducible closed source to an actual B-copy in the SAME C.

The new exact proposition `SourceDefinedStrictAndDomainReflectingConclusion A B D κ n` uses **the same C, p and n** and keeps the Ramsey arrow, strict genuine functional local B-trees and internal B-copies. The only change is an explicit decomposition of the full global map into:

- genuine 2019 source-defined `IsOriginalPartialHomomorphismEmbedding C D p` (equivalent to EHN on this legacy nonempty-defined encoding); and
- domain reflection for **all** primitive function symbols F and tuples x in C:
  `Nonempty(F_D(p x)) → Nonempty(F_C(x))`.

`historicalThreeClauses_iff_sourceDefinedStrictReflected` proves the iff *by reusing the identical witnesses*, not by replacing a weak carrier by its closure, using loose trees, or switching to relational graph-locality. It does **not** establish the existential target in general.

## New finite nonvacuity test

The real three-point/two-point/one-point **binary first-projection algebra** from `PublishedTotalBinaryObstruction` satisfies the Ramsey input. In `unavoidable_domain_loss_for_corrected_Bcover`, **any** C with the actual two-colour Ramsey arrow, internal B-copy extension and a fixed genuine 2019 source-defined map p to the three-point control must have at least one input x where `F_C(x)` is undefined and `F_D(p x)` is defined. This rules out global total-fibre reflection even **without** a strict local tree assumption.

`actual_corrected_Bcovered_RamseyWitness_loses_domain` instantiates the separately verified ALL-ARITY `sparseningRamsey_functional_looseFullTrees` construction and witnesses the phenomenon on a **genuine finite C** satisfying the full functional Ramsey arrow and internal B-copy extension, whose global map is EHN and whose C is a loose full-functional B-tree. This is not a vacuous hypothesis or a made-up structure. No uniform mixed-root schema is used.

Consequently, `no_strictAndReflected_candidate_for_binary_Ramsey` refutes the historical full-functional triple at **every n**, equivalently to the existing direct counterexample.

## Boundaries, not to overclaim

- **The current `main.tex` theorem `thm:sparseningRamsey` is RELATIONAL** and already separately verified; neither the new binary obstruction nor the logical iff refutes it.
- The corrected native n-pass theorem gives strict **graph** B-tree locality. The ALL-ARITY loose-tree theorem yields genuine full-function **loose** trees. Neither yields the missing strict full-functional local trees by definition.
- The upstream 2019 sparse witness supplies relative tagged OLD/U-closed H-completions on the exact tested S. The Ramsey-class conclusion requires the separately explicit `hLocal` axiom; this endgame audit does not derive it from intrinsic weak local-finiteness.
- Because the literal historical global map is refuted, the *corrected* strict full-functional problem should NOT demand that map. Its open issue is the history-sensitive mixed-root relative completion, allocated to Track D.

## CI gate

The new file is imported by a root `CheckAxioms*.lean`, which the full repository workflow builds and audits. Do not merge or annotate `\\leanverified` until the **exact PR head** has green full build and named axiom checks. No author manuscript text or TODO markers are changed.

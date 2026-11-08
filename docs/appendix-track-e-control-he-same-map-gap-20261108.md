# Appendix A Track E — global control map HE gap (8 November 2026)

**Scope:** New Lean source, named axiom audit and this explanatory note only. The survey's main and appendix mathematical prose remains frozen. No previously removed author TODOs are restored.

## What the upstream constructed witness actually provides

The exact verified/merged upstream theorem `AllThoseRamseyClasses.Published.genuinePartite2019_actual_native_sparse_witness_with_H_completions` (PR #924) produces:

- an ACTUAL finite tagged 2019 C, its U-closed/protected canonical B coverage, original cutoff n and exact relative H-valued weak completions;
- a true **native part-preserving** Ramsey arrow on its decoded genuine native carrier; and
- a specific **source-defined original-2019 partial HOMOMORPHISM** `f` to the original native control C0, preserving its vertex parts.

The exported first clause is **not** yet a native `IsOriginalPartialHomomorphismEmbedding`. The predecessor `wholeMaskOriginalDecode_originalPartialControl_of_tagHom` proves original partial hom preservation and part labels from the tagged map. For a HE, the **same f** must restrict to a FULL embedding of **each native irreducible full source E**. Track E #556 shows the equivalent full canonical Option(Set) irreducible-test clause on f, but it is not present in #924's exported theorem.

## Non-vacuous checked counterexample proposed here

The binary left-projection language `F(x,y)={x}` has no relations, with A=1 point, B=2 points, D=3 points. The actual verified corrected loose-tree Ramsey construction supplies a finite C with:

- the genuine 2-colour Ramsey arrow `C → (B)^A_2`;
- internal irreducible B-copy extension;
- a real full-functional loose B-tree; and
- a GOOD 2019 source-defined HE `p:C→D`.

On the **same C and same D**, consider the constant map `q(x)=0`.

`constant_projection_is_originalPartialHom` proves `q` is genuinely source-defined original-partial: any nonempty source output fibre has whole image `{0}`, which equals `F_D(q x,q y)`; undefined inputs remain unrestricted. But `constant_projection_not_originalPartialHE_of_Bcopy` proves `q` cannot reflect a genuine B copy: the irreducible B has two distinct vertices that would have the identical image 0. The Ramsey arrow itself provides such a B-copy.

The theorem `actual_Ramsey_Bcovered_goodHE_and_badHom_same_C` exhibits BOTH maps **on the identical finite C** and verifies all Ramsey, covering and loose-tree properties. The final `actual_bad_projection_genuinePartialHom_not_canonicalHE` checks the same distinction in the faithful Option(Set) target syntax via merged Track E #556.

**This does not refute the possible stronger HE property of the PARTICULAR global f chosen by the 2019 two-pass algorithm.** It proves that the available exported facts `sourceDefinedHom(f)` plus Ramsey arrow plus B-coverage do NOT imply HE(f); selecting a different good p cannot replace the asserted same-map obligation.

## Remaining positive HE task

On the **same actual constructed tagged C and global f**, prove that every native irreducible full E embedding into `(wholeMaskOriginalDecode C).collapseDomain` restricts f to a FULL embedding into C0. Likely relevant additional inputs: the stronger tagged `IsInducedClosedUHomomorphismEmbedding` map still present before the existing final-decoder projection and the protected closed U-irreducible B-copy coverage. One must explicitly bridge the intrinsic native irreducible E and the ambient OLD tagged U-closed/U-irreducible test on its exact carrier; DO NOT silently replace E by its U-generated hull.

The full-functional historical **total-fibre** map remains refuted (PR #544); that is separate from the corrected source-defined HE and from strict functional mixed-root trees (Track D). Intrinsic-versus-ambient class H completion transfer is Track C.

## Validation

All new claims are proof candidates pending the exact-head full repository Lean build and named standard-axiom check in `CheckAxiomsTrackEGlobalControlHEGap.lean`. No `sorry`, `admit` or new axiom is added.

# Appendix A — Track E: derive native normality of the final covered OLD decoder

**6 November 2026.** Independent new-file-only continuation of the validated Track E statement audit and merged [#556](https://github.com/janhubicka/partite-construction/pull/556) / [#562](https://github.com/janhubicka/partite-construction/pull/562). Frozen survey prose and author-maintained TODO markers are untouched.

## Mathematical issue

The verified coordinated 2019 two-pass route constructs a final U-closed tagged OLD **relational** picture with protected canonical B-copy coverage. The already verified `wholeMaskOriginalDecode C` recovers genuine independent-domain `Option(Set)` partial functions, including possible `some ∅`. A native `Structure L V` cannot represent `some ∅`: its empty set fibre means **undefined**. Merged Track E #552 proved the exact characterization `NoDefinedEmptyValues P ↔ P.collapseDomain.toNonemptyPartial = P`; merged #562 made the Ramsey-arrow transfer conditional on this one normality property.

## New candidate proof: protected B-coverage itself discharges native normality

**Key lemma:** `RelStructure.wholeMaskValue_nonempty_of_closed_coverage`. If the final tagged C is U-closed and every U-closed U-irreducible test embedding in C embeds into canonical B, and B has `NoDefinedEmptyValues`, then **every complete OLD graph value witness** `HasWholeMaskValue (wholeMaskTagReduct C) F x U` has a nonempty U.

Proof uses exactly one complete OLD relation tuple `t : Fin(m+q.size)→V`:

1. Its **literal tuple-support** `Set.range t` induces an ordinary irreducible source; this is already `relationTuple_range_irreducible`.
2. `weak_irreducible_embeds_base_of_closed_coverage` uses the *actual* U-closed/U-irreducible protected B-test hypothesis to obtain an induced full embedding of the exact supported test into canonical B.
3. Reflect the **complete OLD value relation** with that full embedding. The definition `wholeMaskPatternGraph` gives a full Base value `some (Set.range outputPositions)`.
4. Since B has no defined-empty operations, that output-position range is nonempty. A chosen index j witnesses an output in the original `U = Set.range (output positions of t)`.

No function-arity positivity, transversal assumption, finite carrier, weak-test hull enlargement, or uniqueness of possible OLD output values enters this key lemma. The quantification remains the *same final C* and *same base B*.

The generic decoder lemma `wholeMaskPartialDecode_noDefinedEmpty_of_closed_coverage` follows because any `some U` is chosen from some actual complete OLD value witness; it also needs no uniqueness or positive arity. The partite specialization `wholeMaskOriginalDecode_noDefinedEmpty_of_closed_coverage` simply forgets unary part predicates without changing functions. With **native B**, the source-normality premise is discharged by `toNonemptyPartial_noDefinedEmpty B`, producing `wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover`.

Finally, `nativeArrow_iff_coveredPartialArrow` combines this output with the kernel-checked normality-gated full Ramsey-arrow equivalence from merged Track E #562:

```text
Structure.Arrow A B (wholeMaskOriginalDecode C).collapseDomain κ
  ↔ GenuinePartialArrow A.toNonemptyPartial B.toNonemptyPartial
      (wholeMaskOriginalDecode C) κ
```

**All assumptions about the final target are the actual 2019 U-closed/protected B-copy coverage assumptions**, not an artificial decoder-normality oracle.

## Important limits

- This proves decoding and arrow-transfer **conditional on an actual final U-closed B-covered tagged picture C**. It does not *construct* that picture or replace the rest of the two-pass theorem's original assumptions.
- It does NOT assert that arbitrary earlier intermediate profiles are normal or function-valued.
- It does NOT prove the original **strict mixed-root full-functional B-tree** sparsening statement; its historical total-fibre global map is independently disproved by the binary counterexample.
- It does NOT replace Track C's class-local completion hypothesis or infer C∈H from local tests. Defined-empty distinctions remain essential for intermediate/weak tests.

## Verification

New Lean module `Functional/TrackECoveredNativeDecoderNoDefinedEmpty2019.lean`, new root `CheckAxiomsTrackECoveredNativeDecoderNoDefinedEmpty2019.lean`; no existing proof implementations or frozen TeX touched. Kernel compilation and exact-head permitted-axiom checks are REQUIRED before any merge or manuscript marker. All declarations are **candidate** until CI passes.

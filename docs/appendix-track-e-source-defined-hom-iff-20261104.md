# Appendix A Track E — source-defined maps commute with faithful partial decoding

**Audit date:** 4 November 2026. Separate new-file-only follow-up to [#552](https://github.com/janhubicka/partite-construction/pull/552), [#544](https://github.com/janhubicka/partite-construction/pull/544), and upstream [#854](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/854).

The native `Structure L V` uses `Set V` as its function fibre, with `∅` encoding UNDEFINED input. The genuine 2019 `PartialSetStructure L V` uses `Option (Set V)` and distinguishes `none` from `some ∅`. The already verified `Structure.toNonemptyPartial` maps only nonempty native fibres to `some S`. Its object and full-embedding essential-image properties were certified in merged #552.

## New exact same-map theorem

`TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial`:

```text
Structure.IsOriginalPartialHomomorphism A B f
    ↔ PartialSetStructure.IsOriginalPartialHomomorphism
        A.toNonemptyPartial B.toNonemptyPartial f
```

This is strictly weaker than the verified full embedding equivalence. The target operation on a SOURCE-UNDEFINED tuple may be defined. On each SOURCE-DEFINED tuple, the entire output set must be equal to the image of the source fibre, not merely contain it. The equivalence retains the **same map f**, source A, target B, arities, and vertex carriers. Its forward direction is the already validated `Structure.IsOriginalPartialHomomorphism.toNonemptyPartial` from `TrackBRealEHNExactImageUSize2019.lean`. The new converse takes exactly the canonical partial source and target and recovers native whole-value equality on source-defined tuples.

`sourceDefined_and_nonreflecting_example` is a concrete unary one-point example: every input is undefined in native source A, every input is defined in native target B, and `id : Unit→Unit` is source-defined-original and genuine-partial-source-defined, but **not** a total-fibre native homomorphism. This rules out silently replacing the global EHN projection by the disproved stronger survey convention.

## Same-map homomorphism-embedding extension

The corrected 2019 global map is a **homomorphism-embedding**, not merely a
source-defined homomorphism. The new `CanonicalEncodedOriginalPartialHE A B f`
retains the original quantification over all **native irreducible structures E**
fully embedded into A. It expresses this test via the canonical genuine-partial
`E.toNonemptyPartial`, using a **FULL** `PartialSetStructure.Embedding` on
each test while allowing the global f to remain source-defined.

`originalPartialHE_iff_canonicalEncodedHE` proves that the exact original
native HE and this canonical Option(Set) HE are equivalent, on the SAME map,
E, and embedded copies. Its proof uses the merged #552 full embedding
equivalence in both directions. `EHN_iff_canonicalEncodedOriginalPartialHE`
composes the established `originalPartialHE_iff_EHN` equivalence, providing a
fully same-witness interface for the actual native EHN projection.

The claim is **not** a blanket equivalence with an irreducibility notion on
arbitrary rich partial Option(Set) structures. In particular, its tests are the
faithful encodings of native irreducibles, not `some ∅` structures with
independent domain predicates.

## Carefully limited scope

- The first theorem concerns **homomorphisms**. The additional exact HE equivalence explicitly quantifies over *canonical encoded native* irreducible source tests and their full embeddings, without changing the original source test category.
- For the native interface, `Structure.originalPartialHE_iff_EHN` already certifies the homomorphism-embedding distinction with the same map. Our composed HE theorem now connects this to genuine-partial canonical native copies. Upstream #854 separately proves the original forward homomorphism direction.
- The original strict mixed-root functional B-tree problem remains separate (Track D). The ambient OLD-relative H local-completion transfer remains separate (Track C).
- This is **not** an end-to-end decoder-normality theorem for arbitrary two-pass profiled relational sparsening outputs, which may carry independent defined-empty inputs.

The frozen survey text, all existing proof implementations, validation markers and author-removed TODOs are untouched. The root `CheckAxiomsTrackESourceDefinedPartialIff.lean` lists all new propositions for the full CI axiom scan; **verification and merge require an exact-head green workflow**.

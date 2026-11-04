# Appendix A Track E — native/partial Ramsey arrow equivalence

**4 November 2026.** Independent, new-file-only follow-up to merged native/Option(Set) full-faithfulness [PR #552](https://github.com/janhubicka/partite-construction/pull/552) and the source-defined HE draft [PR #556](https://github.com/janhubicka/partite-construction/pull/556).

The already verified map equivalence `TrackENativePartialFullFaithfulness.nativePartialFullEmbeddingEquiv` preserves the **same** vertex functions. This module checks the missing compositional compatibility and transports entire Ramsey arrows between the three **canonical** sources A, B and witness C.

## Exact contracts

`toNonemptyPartial_comp` proves the full embedding of the native composition equals composition of the two corresponding canonical genuine-partial full embeddings. No finiteness/arity/single-value hypotheses are added.

`GenuinePartialArrow A B C κ` is a convenient **unpartite** true `Option(Set)` arrow, defined using full embeddings (and `PartialSetStructure.Embedding.comp`) rather than weak homomorphisms. All domain bits and complete output fibres of each copy are preserved.

`arrow_iff_canonicalNonemptyPartial` proves the literal iff

```
Structure.Arrow A B C κ ↔
  GenuinePartialArrow A.toNonemptyPartial B.toNonemptyPartial
    C.toNonemptyPartial κ
```

The direction native→genuine uses all three embedding equivalences `ΦAB`, `ΦBC`, `ΦAC`; the converse uses their inverses. The two Ramsey monochromaticity statements are related by the **same naturality identity**, not by a projection changing the test carrier. No Ramsey arrow is claimed for an arbitrary output of the coordinated 2019 two-pass profile construction.

## Conditional final target decoder

`arrow_iff_partialTarget_of_noDefinedEmpty` is the precise final target
normality-gated arrow transfer: for a genuine `PartialSetStructure P`
whose **every defined operation has a nonempty output set**,
```
Structure.Arrow A B P.collapseDomain κ
  ↔ GenuinePartialArrow A.toNonemptyPartial B.toNonemptyPartial P κ
```
The proof uses the already verified iff
`NoDefinedEmptyValues P ↔ P.collapseDomain.toNonemptyPartial = P` from
merged PR #552 and the native/canonical arrow equivalence in the same
module. It preserves A, B, the exact P carrier and all A/B copy embeddings,
and creates no new Ramsey witness. The condition is an explicit premise,
not a declaration that any two-pass profiled OLD-relational output satisfies
it. Another decoder obligation is still needed to recover a genuine
`PartialSetStructure P` in the first place.

## Why this is useful—and what remains open

This closes the finite-**copy/colouring** semantic boundary between native full functions and genuine partial functions. For any **verified normal** final target, the Ramsey arrow can now be transported back without a new combinatorial proof. It does NOT show that an arbitrary intermediate OLD-relational U-closed sparse witness is itself a canonical functional normal target.

In particular, `PartialSetStructure` can distinguish `some ∅` from `none`. The two-pass construction's final decoder normality is an independent obligation; so are the strict mixed-root functional B-trees (Track D), local class H completion transfer (Track C), and any part-labelled Ramsey class theorem not obtained from this unpartite lemma.

No frozen TeX, prose, TODO, or existing proof implementation has been modified. A root `CheckAxiomsTrackECanonicalArrowEquivalence.lean` checks every new theorem under complete CI. Keep this draft unmerged until exact-head build and named axiom scan are green.

# Appendix A — Track E native ⇄ genuine-partial interface audit (3 Nov 2026)

This is an independent **new-file-only** Track E continuation, after the merged exact theorem-contract PRs [#537](https://github.com/janhubicka/partite-construction/pull/537) and [#544](https://github.com/janhubicka/partite-construction/pull/544). Frozen manuscript prose and author-maintained TODOs are untouched.

## Reuse the existing canonical translation

**Do not define a second native-to-Option conversion.** The dependency has `Structure.toNonemptyPartial`, `Structure.Embedding.toNonemptyPartial` in `Functional/NativeWholeWeakFreeAmalgam.lean` and the literal `A.toNonemptyPartial.collapseDomain=A` in `Functional/NativePartialClosure.lean`. All are already verified. The upstream [lean-all-those-ramsey-classes #846](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/846) currently duplicates the translation and its forward embedding; that PR has received a specific code reuse suggestion.

## New theorem contracts

| Contract | New Lean name | Scope |
|---|---|---|
| `Option.getD` commutes with pointwise set image | `option_getD_image` | All option values, including `some ∅`, all arities, non-injective maps |
| Any partial full embedding **between the canonical native images** gives a native full embedding on exactly the same map | `partialFullEmbedding_toNative` | Actual native source and target; not arbitrary partial objects |
| Native full embeddings and partial full embeddings between canonical images form a literal `Equiv` | `nativePartialFullEmbeddingEquiv` | Same carriers and exact values, both directions |
| All canonically encoded native objects have no defined-empty fibres | `toNonemptyPartial_noDefinedEmpty` | No new domain bit |
| A genuine partial P is in the canonical image on the same carrier iff it has **no** defined-empty values | `noDefinedEmpty_iff_nativeRoundtrip` | Full independent-domain objects, not assumed transversality |
| The one-point genuine defined-empty unary operation is outside the canonical image | `definedEmptyExample_not_nativeImage` | Concrete negative sanity test |

These do not imply that the **outputs** of the coordinated 2019 profiled relational sparsening algorithm remain in the native nonempty-defined subcategory. That is still a separate **decoder normality** obligation. Nor does equivalence of FULL embeddings imply domain reflection for source-defined global EHN maps.

## Validation

Run full project build and the root `CheckAxiomsTrackENativePartialFullFaithfulness.lean` on the precise PR head. The first submitted proof is a candidate until complete CI plus named axiom scan passes. No `sorry`, new axiom, or non-Track-E implementation rewrite is intended.

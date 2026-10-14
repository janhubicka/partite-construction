# Original-partial functional sparsening: exact mixed-root step

**Scope (15 October 2026).** This is the genuine set-valued-function
iteration of the author-supplied published Appendix A, **not** the independent
U-closed recursive proof. Every finite test is counted by its exact vertex
set, and weak restriction means `F^(X|^w_S)(a)=F^X(a) ∩ S`.

## What is formally established

The native EHN induced construction gives full-function Ramsey embeddings,
its global part map is a homomorphism-embedding under the original **partial**
2019 semantics, and `inducedConstruction_weakTree_and_projectedCover` carries
both controlled n-vertex **function-GRAPH** B-tree completions and projected
irreducible B-coverage through the same actual functional Pictures.
`sparseningRamsey_nativeFunctional_graphStrict_withBCover` finishes genuine
B-copy extension without losing that local graph bound. No condition here
asserts full-function strict target trees.

For an exact *closed* test of a binary native attachment
`C = Core *_R Copy`, `closedTestPullback` constructs a full free decomposition
of the test into closed `Left`, `Right` and `Common`. The source common root
has a canonical EHN map `q : Common → A`, and composing with a full
`A ↪ B` gives a **strict original-partial one-copy** completion of the root,
even when `Common` is reducible:
`native_closed_separator_originalPartial_oneCopy`.

## New, precisely conditional one-copy extension criterion

For a full functional free amalgam `X = L *_R M`, suppose `l : L → B` and
`m : M → B` are EHN homomorphism-embeddings agreeing on *exactly the same
source root*, i.e. `l ∘ i_L = m ∘ i_M`. These maps may have image collisions
between otherwise distinct sides. By the existing
`IsFreeAmalgam.exists_EHN_projection`, there is a global EHN map
`X → B`; this gives an **original-partial** homomorphism-embedding into
one genuine B copy. No full-fibre domain reflection is asserted.

The specialized
`closedTest_originalPartial_oneCopy_of_compatible_side_lifts` applies this
to the actual native pullback, requiring both side maps into A to agree with
the **canonical** `q`; compose the map to A with `A ↪ B`.
A second sufficient criterion,
`closedTest_originalPartial_oneCopy_of_core_and_copy_lifts`,
takes the new core's EHN map to A as supplied and needs **only** a compatible
EHN lift for the old-copy side. The genuine Hales–Jewett core naturally
carries such a map into its selected A. The side lift is *not* asserted to
exist: vertices of the old side may have parts outside the selected A-copy.

## Unresolved obligations for strict full-functional sparsening

1. General mixed tests need compatible root-isolated **B-tree side
   extensions** over one fixed completion of the *reducible* separator.
   Arbitrary independently chosen completions cannot simply be identified.
   A single target-A lift for the old side is a useful sufficient special
   case, not a general solution.
2. In the small projected-image case, the strict pullback applies to the
   exact **weak projected image of the particular closed source test**, if
   this image has a strict completion. Do not demand this for all weak
   induced tests: `weakOrderedXY_no_originalPartialTreeCompletion`
   refutes that stronger claim already inside a single ordered B-copy.
3. The complete-function-image homomorphism semantics of the recent survey
   are stronger than the original 2019 partial-function homomorphism
   semantics. The checked full-fibre counterexample must be respected.

The relative tree-extension gluing theorem
`closedTest_treeCompletion_of_sharedRootHistories` already formalizes
the final gluing *conditional on compatible relative witnesses*.
The actual construction of those witnesses for arbitrary reducible roots is
the mathematical step that remains open. No proof should bypass it by taking
function-generated closures of weak tests (which would break the n-vertex
induction).

import PartiteConstruction.Functional.OriginalPartialStarAttachment

/-!
# Restrict a strict original-partial B-tree completion along a tested anchor

A full function-language closed test in the old Picture may intersect the
distinguished Hales--Jewett core in a smaller CLOSED anchor.  A relative
strict original-2019 partial-function completion of the ambient Picture
restricts to that test, anchored at precisely this intersection.

There is no generated-hull enlargement and no need to assume that the
anchor or its projection is injective or irreducible.  The only input
is a commuting triangle of FULL structure embeddings.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H0 H1 E F VB G : Type v}

/-- Restrict a relative original-partial strict tree completion to a
fully embedded tested substructure, while shrinking the original anchor
by a full embedding.  The prescribed root map is the composite q of
the original anchor labels with the embedding of the local anchor.
No weak induced substructures or function-image closure are added. -/
theorem HasOriginalPartialTreeExtensionCompletion.restrict_to_pulled_anchor
    {Anchor : Structure L H0}
    {LocalAnchor : Structure L H1}
    {Prior : Structure L E}
    {Local : Structure L F}
    {Start : Structure L G}
    (Base : Structure L VB)
    (anchor : Embedding Anchor Prior)
    (q : H0 → G)
    (hPrior : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base anchor q)
    (testedIn : Embedding Local Prior)
    (localAnchor : Embedding LocalAnchor Local)
    (toOriginal : Embedding LocalAnchor Anchor)
    (hFactor : ∀ x : H1,
      testedIn (localAnchor x) = anchor (toOriginal x)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base localAnchor (q ∘ toOriginal) := by
  obtain ⟨Y, Target, hExt, p, hp, hRoot⟩ := hPrior
  refine ⟨Y, Target, hExt, p ∘ testedIn, ?_, ?_⟩
  · exact hp.comp testedIn.isEHNHomomorphismEmbedding.toOriginalPartial
  · intro x
    change p (testedIn (localAnchor x)) =
      hExt.startEmbedding (q (toOriginal x))
    rw [hFactor x]
    exact hRoot (toOriginal x)

/-- A star-shaped new functional attachment over a tested part of
the ORIGINAL HJ core: a relative completion of the earlier entire
Picture can be restricted to the local closed anchor.  A relative
completion of the incoming copied side over its canonical root then
preserves that same local anchor in the enlarged strict B-tree.

This is a conditional geometric step; it does NOT assert the required
incoming copied-side relative witness for arbitrary multi-generated
mixed separators. -/
theorem IsFreeAmalgam.originalPartialTreeExtension_append_over_pulled_anchor
    {H : Type v} {Z : Type v}
    {Anchor : Structure L H0}
    {LocalAnchor : Structure L H1}
    {Root : Structure L H}
    {Prior : Structure L E}
    {Left : Structure L F}
    {Right : Structure L Z}
    {Whole : Structure L G}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    {G0 : Type v} (Start : Structure L G0)
    (originalAnchor : Embedding Anchor Prior)
    (q : H0 → G0)
    (testedIn : Embedding Left Prior)
    (localAnchor : Embedding LocalAnchor Left)
    (toOriginal : Embedding LocalAnchor Anchor)
    (hFactor : ∀ x : H1,
      testedIn (localAnchor x) = originalAnchor (toOriginal x))
    (rootInAnchor : Embedding Root LocalAnchor)
    (hRoot : ∀ x : H, sL x = localAnchor (rootInAnchor x))
    (hPrior : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base originalAnchor q)
    (hCopy : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base sR ((q ∘ toOriginal) ∘ rootInAnchor)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base (iL.comp localAnchor) (q ∘ toOriginal) := by
  have hLeft : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base localAnchor (q ∘ toOriginal) :=
    HasOriginalPartialTreeExtensionCompletion.restrict_to_pulled_anchor
      Base originalAnchor q hPrior testedIn localAnchor toOriginal hFactor
  exact hSrc.originalPartialTreeExtension_append_over_anchor
    Base Start localAnchor (q ∘ toOriginal) rootInAnchor
    hRoot hLeft hCopy

end StructuralRamsey.Structure

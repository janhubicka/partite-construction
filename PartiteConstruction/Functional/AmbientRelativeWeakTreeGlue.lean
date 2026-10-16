import PartiteConstruction.Functional.AmbientRelativeWeakAmalgamGlue
import PartiteConstruction.Functional.TreeExtension

/-!
# Gluing strict FUNCTIONAL B-tree extensions over ONE completed WEAK root

This packages the correct target-side step in the genuine native
Hales-Jewett mixed Picture induction, after the independently proved
weak free-amalgam decomposition and relative weak HE gluing.

The source is a FULL functional free amalgam and the weak tested
subset S is completely arbitrary. The common root is exactly the
inverse image of S under the original full root embedding; it is NOT
required to be function closed and is NEVER enlarged to its hull.

Choose:
  * one genuine strict functional B-tree Start,
  * a possibly NONINJECTIVE map q from the exact WEAK common root
    to the vertex carrier of Start;
  * strict full-functional tree extensions of the SAME Start for
    the two sides, whose ambient-relative weak HE maps agree with
    q on the actual weak root.

The existing TreeExtension.mergeFree merges the two strict targets;
full target embeddings preserve ambient-relative weak functional
HEs, including complete multivalued fibres on retained inputs.
The exact weak HE gluing theorem then supplies a single map of
the tested whole into the resulting genuine strict B-tree.

The theorem is CONDITIONAL on the existence of these compatible
side extensions. It is not the false arbitrary-stage hard-root
extension schema refuted by the five-cycle example, and it does
not claim that independently obtained side trees can be identified.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C VB G VL VR : Type v}

/-- The weak common-root restriction of an arbitrary tested vertex
set of a full functional free amalgam is sufficient for genuine
strict B-tree gluing, once compatible relative extensions of ONE
completed root tree have been chosen.

No embedding of the weak root in Start is required: q may collapse
vertices as permitted by the original-2019 partial-function
homomorphism-embedding convention, avoiding false fixed-core
identifications. All source/target operations remain genuinely
set-valued and functional. -/
theorem ambientRelativeWeakTree_glue_sharedRoot
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (Base : Structure L VB)
    (Start : Structure L G)
    (hStart : TreeAmalgam Base G Start)
    (q : ((iL.comp sL) ⁻¹' S) → G)
    (TL : Structure L VL) (TR : Structure L VR)
    (hExtL : TreeExtension Base Start VL TL)
    (hExtR : TreeExtension Base Start VR TR)
    (fL : (iL ⁻¹' S) → VL)
    (fR : (iR ⁻¹' S) → VR)
    (hL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S) TL fL)
    (hR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S) TR fR)
    (hRootL : ∀ (d : H) (hdL : iL (sL d) ∈ S),
      fL ⟨sL d, hdL⟩ =
        hExtL.startEmbedding (q ⟨d, hdL⟩))
    (hRootR : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fR ⟨sR d, hdR⟩ =
        hExtR.startEmbedding (q ⟨d, hdL⟩)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : S → Z,
        IsAmbientRelativeWeakHE Whole S Target f := by
  classical
  obtain ⟨Z, Target, hAll, eL, eR, _hFree, hStartL, hStartR⟩ :=
    hExtL.mergeFree hExtR
  have hTree : TreeAmalgam Base Z Target :=
    hAll.toTree hStart
  have hWholeL : IsAmbientRelativeWeakHE
      Left (iL ⁻¹' S) Target (eL ∘ fL) :=
    hL.postcomp_full eL
  have hWholeR : IsAmbientRelativeWeakHE
      Right (iR ⁻¹' S) Target (eR ∘ fR) :=
    hR.postcomp_full eR
  have hAgree : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      (eL ∘ fL) ⟨sL d, hdL⟩ =
        (eR ∘ fR) ⟨sR d, hdR⟩ := by
    intro d hdL hdR
    change eL (fL ⟨sL d, hdL⟩) =
      eR (fR ⟨sR d, hdR⟩)
    rw [hRootL d hdL, hRootR d hdL hdR]
    exact (hStartL (q ⟨d, hdL⟩)).trans
      (hStartR (q ⟨d, hdL⟩)).symm
  obtain ⟨f, hMap, _hfL, _hfR⟩ :=
    hSrc.ambientRelativeWeakHE_glue S Target
      (eL ∘ fL) (eR ∘ fR)
      hWholeL hWholeR hAgree
  exact ⟨Z, Target, hTree, f, hMap⟩

end StructuralRamsey.Structure.IsFreeAmalgam

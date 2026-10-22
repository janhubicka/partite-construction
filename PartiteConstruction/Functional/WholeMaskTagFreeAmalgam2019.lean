import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019
import PartiteConstruction.Functional.CanonicalTagFreeAmalgam2019

/-!
# Full complete-mask closure tags preserve relational free amalgams

The 2019 complete-mask expansion remembers ALL old domain and output
relations and adds a tag only when the displayed complete output tuple
has a FULL old input-root embedding. The entire input root occurs in the
prefix of the output tuple. Therefore, if the old tuple of a tag lies
on one side of a genuine relational free amalgam, the root embedding
factors through the same side. This holds on the SAME vertex carriers
and for all output masks and equality patterns, including empty old
function domains. It adds no temporary closure vertices.

This is a SOURCE free-amalgam theorem, not a proof of compatible strict
functional target completions for the maximal mixed induction step.
-/

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {H E F C : Type v}

/-- A FULL relational free amalgam of old complete-mask function
graphs remains a free amalgam after fresh 2019 FULL-root complete-mask
tags are added. Full input-root patterns factor through one side
because their complete root is displayed in the tag's argument tuple. -/
theorem wholeMaskTagExpansion
    {Root : RelStructure (L.wholeMaskPatternLanguage P) H}
    {Left : RelStructure (L.wholeMaskPatternLanguage P) E}
    {Right : RelStructure (L.wholeMaskPatternLanguage P) F}
    {Whole : RelStructure (L.wholeMaskPatternLanguage P) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam sL.wholeMaskTag sR.wholeMaskTag
      iL.wholeMaskTag iR.wholeMaskTag := by
  classical
  refine {
    covers := hFree.covers
    overlap := hFree.overlap
    rel_iff := ?_
  }
  intro R z
  rcases R with R | p
  · exact hFree.rel_iff R z
  · constructor
    · rintro ⟨hOld, eRoot, hRoot⟩
      rcases (hFree.rel_iff (.inr (.inr (p.input, p.mask))) z).mp hOld with
        ⟨t, htOld, ht⟩ | ⟨t, htOld, ht⟩
      · have hRange : ∀ j : Fin p.input.rootSize,
            ∃ a : E, eRoot j = iL a := by
          intro j
          refine ⟨t (Fin.castAdd p.mask.size j), ?_⟩
          calc
            eRoot j = z (Fin.castAdd p.mask.size j) := (hRoot j).symm
            _ = iL (t (Fin.castAdd p.mask.size j)) :=
              congrFun ht (Fin.castAdd p.mask.size j)
        let rootLeft : Embedding p.root Left :=
          eRoot.factorThroughRangeHeterogeneous iL hRange
        have hFactor (j : Fin p.input.rootSize) :
            eRoot j = iL (rootLeft j) :=
          Classical.choose_spec (hRange j)
        have hSide : (wholeMaskTagExpansion Left).rel (.inr p) t := by
          refine ⟨htOld, rootLeft, ?_⟩
          intro j
          apply iL.injective
          calc
            iL (t (Fin.castAdd p.mask.size j)) =
                z (Fin.castAdd p.mask.size j) :=
              (congrFun ht (Fin.castAdd p.mask.size j)).symm
            _ = eRoot j := hRoot j
            _ = iL (rootLeft j) := hFactor j
        exact Or.inl ⟨t, hSide, ht⟩
      · have hRange : ∀ j : Fin p.input.rootSize,
            ∃ a : F, eRoot j = iR a := by
          intro j
          refine ⟨t (Fin.castAdd p.mask.size j), ?_⟩
          calc
            eRoot j = z (Fin.castAdd p.mask.size j) := (hRoot j).symm
            _ = iR (t (Fin.castAdd p.mask.size j)) :=
              congrFun ht (Fin.castAdd p.mask.size j)
        let rootRight : Embedding p.root Right :=
          eRoot.factorThroughRangeHeterogeneous iR hRange
        have hFactor (j : Fin p.input.rootSize) :
            eRoot j = iR (rootRight j) :=
          Classical.choose_spec (hRange j)
        have hSide : (wholeMaskTagExpansion Right).rel (.inr p) t := by
          refine ⟨htOld, rootRight, ?_⟩
          intro j
          apply iR.injective
          calc
            iR (t (Fin.castAdd p.mask.size j)) =
                z (Fin.castAdd p.mask.size j) :=
              (congrFun ht (Fin.castAdd p.mask.size j)).symm
            _ = eRoot j := hRoot j
            _ = iR (rootRight j) := hFactor j
        exact Or.inr ⟨t, hSide, ht⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact (iL.wholeMaskTag.map_rel_iff (.inr p) t).mpr ht
      · exact (iR.wholeMaskTag.map_rel_iff (.inr p) t).mpr ht

end StructuralRamsey.RelStructure.IsFreeAmalgam

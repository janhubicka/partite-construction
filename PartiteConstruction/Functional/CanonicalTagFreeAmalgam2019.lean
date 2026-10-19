import PartiteConstruction.Functional.NativeTaggedWeakPreimage
import PartiteConstruction.Ramsey.ClosureEmbeddingRange
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Complete FULL function-root tagging preserves exact free amalgamation

Let Root, Left, Right, Whole be OLD equality-pattern relational
structures for partial set-valued functions, including active
domain-root and output-graph relations. Suppose their FULL maps
form a genuine relational free amalgam.

Their canonical tagged structures add one FRESH closure relation
for each complete FULL OLD active input-root pattern, on the SAME
vertices. Every tagged output tuple in Whole has a true OLD graph
tuple, which lies entirely on one side. Its complete FULL root
embedding factors back through that side, because every root
vertex is a displayed coordinate of that graph tuple.
Consequently its fresh tag holds on that side too.

This shows the canonical full-pattern tagging construction
preserves the complete SOURCE free-amalgam diagram. It neither
constructs a strict B-tree target completion nor assumes
compatibility of independent relative target-root histories.
-/

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- An OLD equality-pattern function-graph full free amalgam stays
a genuine relational free amalgam after adding fresh canonical
FULL input-root closure tags, one per COMPLETE active root.

The tagged source carries EXACTLY the original vertices.
The full root pattern has carrier Fin n which may live in a
different universe from the ambient sides; root factorization
uses the previously verified heterogeneous-range lemma.
No singleton-valuedness, extra root closure, or generated
test vertices are assumed. -/
theorem patternTagExpansion
    {Root : RelStructure (L.patternGraph) H}
    {Left : RelStructure (L.patternGraph) E}
    {Right : RelStructure (L.patternGraph) F}
    {Whole : RelStructure (L.patternGraph) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam sL.patternTag sR.patternTag
      iL.patternTag iR.patternTag := by
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
      rcases (hFree.rel_iff (.inr (.inr p.input)) z).mp hOld with
        ⟨w, hwOld, hw⟩ | ⟨w, hwOld, hw⟩
      · have hRange : ∀ j : Fin p.input.rootSize,
            ∃ a : E, eRoot j = iL a := by
          intro j
          refine ⟨w j.castSucc, ?_⟩
          calc
            eRoot j = z j.castSucc := (hRoot j).symm
            _ = iL (w j.castSucc) := congrFun hw j.castSucc
        let g : Embedding p.root Left :=
          eRoot.factorThroughRangeHeterogeneous iL hRange
        have hFactor (j : Fin p.input.rootSize) :
            eRoot j = iL (g j) :=
          Classical.choose_spec (hRange j)
        have hSideTag :
            (RelStructure.patternTagExpansion Left).rel (.inr p) w := by
          refine ⟨hwOld, g, ?_⟩
          intro j
          apply iL.injective
          calc
            iL (w j.castSucc) = z j.castSucc :=
              (congrFun hw j.castSucc).symm
            _ = eRoot j := hRoot j
            _ = iL (g j) := hFactor j
        exact Or.inl ⟨w, hSideTag, hw⟩
      · have hRange : ∀ j : Fin p.input.rootSize,
            ∃ a : F, eRoot j = iR a := by
          intro j
          refine ⟨w j.castSucc, ?_⟩
          calc
            eRoot j = z j.castSucc := (hRoot j).symm
            _ = iR (w j.castSucc) := congrFun hw j.castSucc
        let g : Embedding p.root Right :=
          eRoot.factorThroughRangeHeterogeneous iR hRange
        have hFactor (j : Fin p.input.rootSize) :
            eRoot j = iR (g j) :=
          Classical.choose_spec (hRange j)
        have hSideTag :
            (RelStructure.patternTagExpansion Right).rel (.inr p) w := by
          refine ⟨hwOld, g, ?_⟩
          intro j
          apply iR.injective
          calc
            iR (w j.castSucc) = z j.castSucc :=
              (congrFun hw j.castSucc).symm
            _ = eRoot j := hRoot j
            _ = iR (g j) := hFactor j
        exact Or.inr ⟨w, hSideTag, hw⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact (iL.patternTag.map_rel_iff (.inr p) w).mpr hw
      · exact (iR.patternTag.map_rel_iff (.inr p) w).mpr hw

end StructuralRamsey.RelStructure.IsFreeAmalgam

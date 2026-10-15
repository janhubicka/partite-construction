import PartiteConstruction.Functional.EHNPowerCanonicalRootOneSided
import PartiteConstruction.Functional.OriginalPartialRelativeAppend

/-!
# Preserve the actual power-core root after the first copied attachment

The published Appendix A Picture construction makes several attachments to
one Hales--Jewett power. The one-sided mixed-test theorem alone gives an
ABSOLUTE strict B-tree completion and forgets the original power core.

The relative append lemma needs precisely the stronger invariant constructed
here: a completion of the full closed mixed test **relative to the original
closed power-core side**, with its canonical selected A-label map into Base.
The old-copy side's relative extension is the sole extra hypothesis.

This is the initial anchored strict completion in the actual native
function-language Picture, not a relational U-closed surrogate. It allows
the next attachment to use OriginalPartialRelativeAppend, but does not
construct the missing old-side relative witness for a multi-generated root.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The first genuine Hales--Jewett closed-test attachment retains the
power-core as a distinguished ANCHOR in a relative strict full-functional
B-tree completion. Its root map is exactly the canonical Hales--Jewett
A-part map composed with A -> Base.

The only assumed witness is the relative extension of the copied old
side over the exact selected A-support label map of the common root.
Unlike the earlier absolute mixed completion, this interface can be
carried through further copied attachments by
`IsFreeAmalgam.originalPartialTreeExtension_append`. -/
theorem closedTest_power_canonicalRoot_anchored_relative_completion
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (alpha : Structure.Embedding A Douter)
    (R : System L U W) (hR : R.WeaklyPartiteOver A)
    (N : ℕ) (hN : 0 < N)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha))
      ((Induced.power R N).relabel alpha.toFunctionEmbedding))
    (Test : Set
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := Induced.Vertex R N) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        ((Induced.power R N).relabel alpha.toFunctionEmbedding)
        f).toStructure.IsClosed Test)
    (hCopy :
      let S := B.support alpha.toFunctionEmbedding
      let hS := B.weak_support_closed Douter hB.1 A alpha
      let pb := closedTestPullback B S hS
        ((Induced.power R N).relabel alpha.toFunctionEmbedding)
        f Test hTest
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toRight
        (eAB ∘ ((B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap))) :
    let S := B.support alpha.toFunctionEmbedding
    let hS := B.weak_support_closed Douter hB.1 A alpha
    let Dsys := (Induced.power R N).relabel alpha.toFunctionEmbedding
    let pb := closedTestPullback B S hS Dsys f Test hTest
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base
      (pb.leftIn.comp (Structure.Embedding.id pb.left))
      ((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap) := by
  let S := B.support alpha.toFunctionEmbedding
  let hS := B.weak_support_closed Douter hB.1 A alpha
  let Dsys := (Induced.power R N).relabel alpha.toFunctionEmbedding
  let pb := closedTestPullback B S hS Dsys f Test hTest
  have hCore : Dsys.toStructure.IsEHNHomomorphismEmbedding Base
      (eAB ∘ (Induced.power R N).part) :=
    Induced.power_relabel_originalPartial_EHN_to_base
      A R hR Douter alpha Base eAB N hN
  have hLeft : pb.left.IsEHNHomomorphismEmbedding Base
      ((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap) :=
    hCore.comp pb.leftMap.isEHNHomomorphismEmbedding
  have hLabel : ∀ x : pb.Common,
      (Induced.power R N).part (pb.leftMap (pb.toLeft x)) =
      (B.weakRestrict Douter hB.1 A alpha).part (pb.commonMap x) :=
    closedTest_power_core_root_label_eq_selected_part
      B Douter hB A alpha R N f Test hTest
  have hRootMaps :
      (((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap) ∘ pb.toLeft) =
      (eAB ∘ ((B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap)) := by
    funext x
    exact congrArg eAB (hLabel x)
  have hCopyCore : HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base pb.toRight
      (((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap) ∘ pb.toLeft) := by
    rw [hRootMaps]
    exact hCopy
  exact pb.free.originalPartialTreeExtension_append
    Base Base
    (Structure.Embedding.id pb.left)
    ((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap)
    Base TreeExtension.refl
    ((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap)
    hLeft.toOriginalPartial (fun _ => rfl) hCopyCore

end StructuralRamsey.FunctionalPartite.Attachment

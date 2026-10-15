import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue
import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-!
# Native functional mixed root: new Hales--Jewett core is automatic

The new core has an EHN projection to A, and A embeds fully into
Base. This provides a strict original-partial B-tree relative witness
over the exact common root with Start=Base and TreeExtension.refl.
No cardinal or generator-rank bound is needed for the new core.

Thus the only additional relative extension witness needed to
complete a genuinely mixed closed test is for the OLD-copy side.
The root may be reducible and its canonical projection noninjective.
This does NOT construct the missing old-copy relative extension.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB : Type v}

/-- If the LEFT side of a full functional free amalgam EHN-maps
to Base, it automatically admits a strict relative B-tree completion
over the root map q=pLeft∘sL with zero attachments. The whole source
completes strictly whenever only the RIGHT side has a relative
witness over that same prescribed root map. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_of_left_EHN_and_right_relative
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (pLeft : E → VB)
    (hLeft : Left.IsEHNHomomorphismEmbedding Base pLeft)
    (hRight : HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base sR (pLeft ∘ sL)) :
    HasOriginalPartialTreeCompletion Base Whole := by
  have hBaseTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun b => ⟨b, rfl⟩)
  have hRelativeLeft : HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base sL (pLeft ∘ sL) := by
    refine ⟨VB, Base, TreeExtension.refl, pLeft,
      hLeft.toOriginalPartial, ?_⟩
    intro x
    rfl
  exact hSrc.originalPartialTreeCompletion_glue_relative
    Base hBaseTree (pLeft ∘ sL) hRelativeLeft hRight

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W VB U : Type v}

/-- For an ACTUAL native full-functional EHN closed-test pullback,
a core EHN map into Base supplies its strict root-relative witness
automatically. One OLD-copy relative witness over the prescribed
canonical root map then completes the mixed closed test strictly. -/
theorem closedTest_originalPartial_strictTree_of_core_EHN_and_copy_relative
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Base : Structure L VB)
    (Test : Set
      (Structure.Attachment.Vertex S
        (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (coreMap : W → VB)
    (hCore : D.toStructure.IsEHNHomomorphismEmbedding Base coreMap)
    (hCopy :
      let pb := closedTestPullback B S hS D f Test hTest
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toRight
        ((coreMap ∘ pb.leftMap) ∘ pb.toLeft)) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B S hS D f).toStructure.induce Test hTest) := by
  let pb := closedTestPullback B S hS D f Test hTest
  have hLeft : pb.left.IsEHNHomomorphismEmbedding
      Base (coreMap ∘ pb.leftMap) :=
    hCore.comp pb.leftMap.isEHNHomomorphismEmbedding
  exact pb.free.originalPartialTreeCompletion_of_left_EHN_and_right_relative
    Base (coreMap ∘ pb.leftMap) hLeft hCopy

/-- In a selected A-support native step, the whole new core EHN
projection to A composed with A↪Base automatically supplies the
core-side relative completion. The common root can be reducible.
Only the copied old side needs a relative extension. -/
theorem closedTest_originalPartial_strictTree_of_selected_core_and_copy_relative
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (alpha : Structure.Embedding A Douter)
    (Dsys : System L P W)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)) Dsys)
    (Test : Set
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.IsClosed Test)
    (gCore : W → U)
    (hCore : Dsys.toStructure.IsEHNHomomorphismEmbedding A gCore)
    (hCopy :
      let S := B.support alpha.toFunctionEmbedding
      let hS := B.weak_support_closed Douter hB.1 A alpha
      let pb := closedTestPullback B S hS Dsys f Test hTest
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toRight
        (((eAB ∘ gCore) ∘ pb.leftMap) ∘ pb.toLeft)) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.induce Test hTest) := by
  have hTarget : Dsys.toStructure.IsEHNHomomorphismEmbedding
      Base (eAB ∘ gCore) :=
    eAB.isEHNHomomorphismEmbedding.comp hCore
  exact closedTest_originalPartial_strictTree_of_core_EHN_and_copy_relative
    B (B.support alpha.toFunctionEmbedding)
      (B.weak_support_closed Douter hB.1 A alpha)
    Dsys f Base Test hTest (eAB ∘ gCore) hTarget hCopy

end StructuralRamsey.FunctionalPartite.Attachment

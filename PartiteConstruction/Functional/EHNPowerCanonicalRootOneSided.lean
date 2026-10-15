import PartiteConstruction.Functional.EHNPowerOneSidedOriginalPartialMixedRoot
import PartiteConstruction.Functional.NativeMixedOriginalPartialOneCopyCriterion

/-!
# The actual power-core common separator has the old A-part labels

In the published native EHN Picture step, the new core is a genuine
Hales--Jewett power of the old stage restricted to the prescribed
A-support, relabelled along alpha:A↪Douter.

The root map needed in the one-sided strict original-partial B-tree
gluing theorem is not an arbitrary choice: on the ACTUAL common
separator it coincides with the old selected support's canonical
A-part projection. This equality follows from the full partite
embedding f and alpha's injectivity, without any assumption that
the root itself is irreducible or that this map is injective.

Consequently the still-missing OLD-COPY relative strict extension
can be formulated over exactly the canonical support map
eAB∘weakRestrict.part∘pb.commonMap. That is the same map already
used in the original published proof's controlled A-copy history.
This alignment is essential before trying to carry a rooted invariant
through the later successive attachments.

This module proves the map equality and reduces strict local
completion of the actual closed power attachment to ONE old-side
relative extension over that canonical map. It does NOT assert that
the latter extension always exists for hard multi-generated roots.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The actual selected A-support labels of the common root agree
pointwise with the Hales--Jewett core part projection. The full
function-closed pullback, not a weak induced approximation, is used. -/
theorem closedTest_power_core_root_label_eq_selected_part
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U)
    (alpha : Structure.Embedding A Douter)
    (R : System L U W)
    (N : ℕ)
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
        f).toStructure.IsClosed Test) :
    let S := B.support alpha.toFunctionEmbedding
    let hS := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B S hS
      ((Induced.power R N).relabel alpha.toFunctionEmbedding)
      f Test hTest
    ∀ x : pb.Common,
      (Induced.power R N).part (pb.leftMap (pb.toLeft x)) =
      (B.weakRestrict Douter hB.1 A alpha).part (pb.commonMap x) := by
  exact closedTestPullback_core_root_agrees_of_labelledCore
    B Douter hB A alpha
    ((Induced.power R N).relabel alpha.toFunctionEmbedding)
    f (Induced.power R N).part
    (fun _ => rfl) Test hTest

/-- The missing old-copy rooted witness for the actual Hales--Jewett
power attachment may be anchored at the CANONICAL old-stage A-support
part map, rather than an independently chosen completion of the root.

The new power core supplies its strict original-partial relative
Base witness automatically and the two compatible maps are glued.
The old-copy relative witness remains an explicit hypothesis. -/
theorem closedTest_originalPartial_strictTree_of_power_and_canonical_copy_relative
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
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        ((Induced.power R N).relabel alpha.toFunctionEmbedding)
        f).toStructure.induce Test hTest) := by
  let S := B.support alpha.toFunctionEmbedding
  let hS := B.weak_support_closed Douter hB.1 A alpha
  let Dsys := (Induced.power R N).relabel alpha.toFunctionEmbedding
  let pb := closedTestPullback B S hS Dsys f Test hTest
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
  exact closedTest_originalPartial_strictTree_of_powerCore_and_copy_relative
    B Douter hB A Base eAB alpha R hR N hN f Test hTest hCopyCore

end StructuralRamsey.FunctionalPartite.Attachment

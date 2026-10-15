import PartiteConstruction.Functional.EHNOneSidedOriginalPartialMixedRoot
import PartiteConstruction.Functional.EHNPictureInvariant

/-!
# Genuine native Hales--Jewett power: canonical one-sided strict root

One EHN Picture step starts with the genuine functional power
E=power R N of the selected weak A-system R. Its relabelling along
alpha:A↪Douter changes only the partition labels, NOT its full
function/relation structure. The power projection remains an EHN
map to A, hence to Base through A↪Base.

Consequently for an exact closed test in the binary native attachment
of an old stage to this genuine power core, a single relative strict
original-partial extension of the copied old side over the prescribed
power root map suffices. No additional relative core extension lemma
or generator budget for the power core is needed.

This result DOES NOT produce the old-side relative witness for
arbitrary maximal multi-generated reducible roots; it records a
precise one-sided proof interface usable in the original two-case
published Picture induction.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V P VB : Type v}

/-- Relabelling the actual positive Hales--Jewett power core along
the selected A-placement leaves its EHN map into Base unchanged.
No full-fibre domain reflection is imposed on this EHN projection. -/
theorem power_relabel_originalPartial_EHN_to_base
    (A : Structure L U)
    (R : System L U V)
    (hR : R.WeaklyPartiteOver A)
    (Douter : Structure L P)
    (alpha : Structure.Embedding A Douter)
    (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (N : ℕ) (hN : 0 < N) :
    ((power R N).relabel alpha.toFunctionEmbedding).toStructure
      .IsEHNHomomorphismEmbedding Base
        (eAB ∘ (power R N).part) := by
  exact eAB.isEHNHomomorphismEmbedding.comp
    (power_weaklyPartiteOver hR hN)

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- In the actual Hales--Jewett core of a selected functional Picture
step, the entire core's EHN projection to A and then Base gives
the relative strict B-tree root witness for FREE.

Thus a mixed genuine CLOSED test only needs an old-copy relative
strict extension over the fixed root map obtained by restricting the
canonical Hales--Jewett power projection to the common separator.
The common separator may be reducible and the root map noninjective. -/
theorem closedTest_originalPartial_strictTree_of_powerCore_and_copy_relative
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
      let Dsys := (Induced.power R N).relabel alpha.toFunctionEmbedding
      let pb := closedTestPullback B S hS Dsys f Test hTest
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toRight
        (((eAB ∘ (Induced.power R N).part) ∘ pb.leftMap) ∘ pb.toLeft)) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        ((Induced.power R N).relabel alpha.toFunctionEmbedding)
        f).toStructure.induce Test hTest) := by
  have hCore : ((Induced.power R N).relabel alpha.toFunctionEmbedding)
      .toStructure.IsEHNHomomorphismEmbedding A
        (Induced.power R N).part :=
    Induced.power_weaklyPartiteOver hR hN
  exact closedTest_originalPartial_strictTree_of_selected_core_and_copy_relative
    B Douter hB A Base eAB alpha
    ((Induced.power R N).relabel alpha.toFunctionEmbedding)
    f Test hTest (Induced.power R N).part hCore hCopy

end StructuralRamsey.FunctionalPartite.Attachment

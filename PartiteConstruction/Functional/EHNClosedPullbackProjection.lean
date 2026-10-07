import PartiteConstruction.Functional.EHNIrreducibleMixedCompletion

/-! # The closed EHN separator has the same labels on both attachment sides

A closed test in a one-copy EHN attachment has a canonical full-functional
pullback.  Its overlap is a closed substructure of the selected A-support.
This lemma checks the *exact* projection equalities on both pullback sides;
they are not additional assumptions on the glued source.

Combined with the EHN root dichotomy and irreducible-root history
completion, it isolates the reducible root as the remaining genuinely
new case of functional strict tree sparsening.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P U V W : Type v}

/-- The canonical common root of a closed binary EHN attachment has one
A-labelling, which induces exactly the same outer projection on both
full-functional pullback sides. -/
theorem closedTestPullback_common_part_compat
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (alpha : Structure.Embedding A Douter)
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
        Dsys f).toStructure.IsClosed Test) :
    let Supp := B.support alpha.toFunctionEmbedding
    let hSupp := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
    let q : pb.Common → U :=
      (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
    ∀ d : pb.Common,
      Dsys.part (pb.leftMap (pb.toLeft d)) = alpha (q d) ∧
      B.part (pb.rightMap (pb.toRight d)) = alpha (q d) := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let WR := B.weakRestrict Douter hB.1 A alpha
  let q : pb.Common → U := WR.part ∘ pb.commonMap
  change ∀ d : pb.Common,
      Dsys.part (pb.leftMap (pb.toLeft d)) = alpha (q d) ∧
      B.part (pb.rightMap (pb.toRight d)) = alpha (q d)
  intro d
  have hLabel :
      alpha (q d) = B.part (pb.commonMap d).1 :=
    B.restrictedPart_spec alpha.toFunctionEmbedding (pb.commonMap d)
  constructor
  · calc
      Dsys.part (pb.leftMap (pb.toLeft d)) =
          Dsys.part (f.toEmbedding (pb.commonMap d)) :=
        congrArg Dsys.part (pb.common_left d)
      _ = B.part (pb.commonMap d).1 := by
        exact f.map_part (pb.commonMap d)
      _ = alpha (q d) := hLabel.symm
  · calc
      B.part (pb.rightMap (pb.toRight d)) =
          B.part (pb.commonMap d).1 := by
        rw [pb.common_right d]
        rfl
      _ = alpha (q d) := hLabel.symm

end StructuralRamsey.FunctionalPartite.Attachment

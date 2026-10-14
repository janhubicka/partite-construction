import PartiteConstruction.Functional.NativeAttachmentOriginalPartialSeparator
import PartiteConstruction.Functional.ProjectedIrreducibleCover

/-!
# The exact native mixed root: a sufficient one-copy extension criterion

The actual common closed separator of a functional EHN binary attachment
has a canonical EHN map into the selected A, hence a strict one-copy
original-partial completion in B whenever A embeds in B.

A one-copy strict completion of the ENTIRE mixed source follows if the
two actual closed sides admit EHN maps into that SAME A extending that
SAME prescribed separator map. A free amalgam then supplies a combined EHN
map to A, and composing with A ↪ B supplies a one-copy B-tree.

This is a conditional *relative extension* criterion, not a proof that
every mixed attachment has the required maps. The core and its sides
remain genuine functional structures; no U-closed relational replay,
weak-test closure enlargement, or total-fibre homomorphism is assumed.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB : Type v}

/-- Two EHN side maps into a single genuine functional B-copy, agreeing
on their full common root, give a strict original-partial one-copy
completion of the whole functional free amalgam. The side maps may
identify vertices outside the root with one another: only the
original partial-function homomorphism-embedding notion is asserted. -/
theorem IsFreeAmalgam.originalPartial_oneCopy_of_compatible_EHN_sides
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L Z}
    {toLeft : Embedding Root Left} {toRight : Embedding Root Right}
    {leftIn : Embedding Left Whole} {rightIn : Embedding Right Whole}
    (hfree : IsFreeAmalgam toLeft toRight leftIn rightIn)
    (Base : Structure L VB)
    (pLeft : E → VB) (pRight : F → VB)
    (hLeft : Left.IsEHNHomomorphismEmbedding Base pLeft)
    (hRight : Right.IsEHNHomomorphismEmbedding Base pRight)
    (hAgree : ∀ x, pLeft (toLeft x) = pRight (toRight x)) :
    HasOriginalPartialTreeCompletion Base Whole := by
  obtain ⟨p, hp, _hLeft, _hRight⟩ :=
    hfree.exists_EHN_projection pLeft pRight hLeft hRight hAgree
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base Base Whole p hp

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- Sufficient lifting condition for the actual closed mixed EHN test:
if both closed pullback sides have EHN maps to the selected control A
extending the SAME canonical root projection, then the whole closed
test has a strict full-functional one-copy B-tree completion in the
ORIGINAL 2019 partial-function sense.

The remaining open task is to construct such maps, or more general
root-isolated strict tree extensions, from the predecessor invariant.
This theorem does not assert their unconditional existence. -/
theorem closedTest_originalPartial_oneCopy_of_compatible_side_lifts
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
    (gLeft :
      (closedTestPullback B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest).Left → U)
    (gRight :
      (closedTestPullback B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest).Right → U)
    (hLeft :
      let pb := closedTestPullback B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest
      pb.left.IsEHNHomomorphismEmbedding A gLeft)
    (hRight :
      let pb := closedTestPullback B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest
      pb.right.IsEHNHomomorphismEmbedding A gRight)
    (hAgree :
      let pb := closedTestPullback B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest
      let q : pb.Common → U :=
        (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
      ∀ x : pb.Common,
        gLeft (pb.toLeft x) = q x ∧
        gRight (pb.toRight x) = q x) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.induce Test hTest) := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let q : pb.Common → U :=
    (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
  have hcompat : ∀ x : pb.Common,
      gLeft (pb.toLeft x) = gRight (pb.toRight x) := by
    intro x
    exact (hAgree x).1.trans (hAgree x).2.symm
  have hL : pb.left.IsEHNHomomorphismEmbedding A gLeft := hLeft
  have hR : pb.right.IsEHNHomomorphismEmbedding A gRight := hRight
  obtain ⟨p, hp, _hpL, _hpR⟩ :=
    pb.free.exists_EHN_projection gLeft gRight hL hR hcompat
  have hToBase :
      ((UnitAttachD B Supp hSupp Dsys f).toStructure.induce Test hTest)
        .IsEHNHomomorphismEmbedding Base (eAB ∘ p) :=
    eAB.isEHNHomomorphismEmbedding.comp hp
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    Base ((UnitAttachD B Supp hSupp Dsys f).toStructure.induce Test hTest)
      (eAB ∘ p) hToBase

end StructuralRamsey.FunctionalPartite.Attachment

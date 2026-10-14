import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.EHNClosedPullbackRootDichotomy

/-!
# Actual native EHN attachment separator has a one-copy partial completion

The 2019 functional iteration splits a closed test of a NATIVE EHN
binary attachment along a closed common separator R.

R may be reducible and its EHN part map into A may not be injective.
Nevertheless, in the ORIGINAL 2019 partial-function sense, its
projection into A followed by a full embedding A ↪ Base gives a
homomorphism-embedding into a SINGLE full functional Base copy.
Hence the common separator has a strict one-copy Base-tree
completion, regardless of reducibility.

This settles existence of a common candidate *root completion*.
The hard remaining functional mixed-step obligation is to construct
TWO relative root-isolated tree extensions of the actual closed
sides that agree with this one root completion, or else choose some
other compatible common strict tree. Independent side completions
do not imply those relative extensions.
No U-closed relational construction or new Ramsey recursion is used.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- For the exact common closed separator of a genuinely functional
EHN attachment, its (possibly noninjective) part projection gives an
original-2019 partial homomorphism-embedding into one Base copy
whenever the selected control A fully embeds in Base. -/
theorem native_closed_separator_originalPartial_oneCopy
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
        Dsys f).toStructure.IsClosed Test) :
    let Supp := B.support alpha.toFunctionEmbedding
    let hSupp := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
    HasOriginalPartialTreeCompletion Base pb.common := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let WR := B.weakRestrict Douter hB.1 A alpha
  have hRoot : pb.common.IsEHNHomomorphismEmbedding A
      (WR.part ∘ pb.commonMap) :=
    closedTestPullback_common_EHN
      B Douter hB A alpha Dsys f Test hTest
  have hBase : pb.common.IsEHNHomomorphismEmbedding Base
      (eAB ∘ (WR.part ∘ pb.commonMap)) :=
    eAB.isEHNHomomorphismEmbedding.comp hRoot
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    Base pb.common (eAB ∘ (WR.part ∘ pb.commonMap)) hBase

end StructuralRamsey.FunctionalPartite.Attachment

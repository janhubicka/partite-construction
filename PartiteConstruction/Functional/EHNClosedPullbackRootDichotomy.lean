import PartiteConstruction.Functional.EHNClosedMixedSize
import PartiteConstruction.Functional.EHNRootDichotomy

/-! # EHN projection on the actual closed attachment separator

The support chosen in a functional EHN Picture step is the preimage of an
A-copy in the outer structure.  Its weak restriction carries the canonical
EHN projection into A.  The common separator of the closed-test free
amalgam pulls back to a genuine closed substructure of this weak restriction.

Hence the separator itself has an EHN projection into A.  If its projection
does not come from a full embedding into A, the separator must have a
proper *full functional* free decomposition.  No hereditary irreducibility
assumption on A, and no weak induced test, is required.

This is the genuine binary-attachment form of the reducible-root dichotomy,
with the actual common pullback used by the subsequent size induction.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P U V W : Type v}

/-- The common part of a closed test in a binary EHN attachment inherits the
canonical weak EHN projection to A through the selected attachment support. -/
theorem closedTestPullback_common_EHN
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
    pb.common.IsEHNHomomorphismEmbedding A
      ((B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap) := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let WR := B.weakRestrict Douter hB.1 A alpha
  have hWR : WR.WeaklyPartiteOver A :=
    B.weakRestrict_invariant Douter hB.1 A alpha hB
  have eRoot : Structure.Embedding pb.common WR.toStructure :=
    pb.commonMap
  exact hWR.comp eRoot.isEHNHomomorphismEmbedding

/-- The actual closed mixed attachment separator either has the full
prescribed A-label embedding, or splits as a proper full free amalgam.
The latter is the only case requiring a shared strict separator tree. -/
theorem closedTestPullback_common_embedding_or_decompose
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
    (∃ g : Structure.Embedding pb.common A, ∀ x, g x = q x) ∨
      Nonempty (ProperFreeDecomposition pb.common) := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let q : pb.Common → U :=
    (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
  have hp : pb.common.IsEHNHomomorphismEmbedding A q :=
    closedTestPullback_common_EHN B Douter hB A alpha Dsys f Test hTest
  by_cases hIrr : pb.common.Irreducible
  · left
    obtain ⟨g, hg⟩ :=
      hp.2 pb.common hIrr (Structure.Embedding.id pb.common)
    refine ⟨g, ?_⟩
    intro x
    calc
      g x = q ((Structure.Embedding.id pb.common) x) := hg x
      _ = q x := rfl
  · right
    by_contra hnone
    exact hIrr
      ((irreducible_iff_noProperFreeDecomposition pb.common).mpr hnone)

end StructuralRamsey.FunctionalPartite.Attachment

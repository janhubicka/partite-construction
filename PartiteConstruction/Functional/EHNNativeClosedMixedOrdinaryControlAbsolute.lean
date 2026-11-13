import PartiteConstruction.Functional.OriginalPartialMixedOrdinaryControlAbsolute
import PartiteConstruction.Functional.EHNClosedPullbackProjection
import PartiteConstruction.Functional.EHNClosedMixedSize

/-!
# Track D: real native mixed closed-test ABSOLUTE strict functional successor

English proof committed BEFORE this Lean module:
docs/track-d-english-actual-native-closed-mixed-absolute-20261112.md

This is an actual one-copy native UnitAttachD, with genuine full
functional EHN projection on both sides and an exact function-closed
tested subset. The old control's ORDINARY rank-m ambient-relative weak
strict B-tree predecessor yields an ABSOLUTE strict original-partial
B-tree completion of each genuinely mixed test of ≤m+1 vertices,
INCLUDING reducible/colliding common roots and nonclosed projected
side images.

The verified full closed pullback has strict source-side cardinal
drop; the canonical selected-A root part compatibility holds without
injectivity. These are the only two new specializations of the parent
ordinary-control marked-gluing theorem.

IMPORTANT: no statement of projected HISTORY preservation for the
completed test or preservation of the rank-m AtMost predecessor across
an entire ordered Hales–Jewett Picture is made. Target mark false
hits at unoccupied A positions remain the hard missing theorem.
Original survey text/TODOs are frozen, unchanged.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The genuine native full-functional ONE-COPY mixed closed-test
rank successor at the level of ABSOLUTE strict B-tree completability.

The old functional control Douter is assumed to have an ordinary
rank-m ambient-relative strict B-tree predecessor. The new old/core
attachment sides must each project to Douter by actual EHN maps;
the support of the copied B is exactly the preimage of one FULL
selected A↪Douter.

The literal test Test is function-closed, genuinely MIXED, and has
≤m+1 vertices. The result permits a NONINJECTIVE/colliding canonical
source-root map and does not demand that either projected side image
be closed in Douter. No test vertices or source generators are added.

This result does NOT return history or source-part projection safety;
therefore it is NOT the still-open full native strict n-pass theorem.
-/
theorem closedTest_originalPartial_weakRankSucc_absolute_mixed
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (alpha : Structure.Embedding A Douter)
    (Dsys : System L P W)
    (hD : Dsys.WeaklyPartiteOver Douter)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)) Dsys)
    (Base : Structure L VB)
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base Douter (id : P → P) m)
    (Test : Finset
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.IsClosed (↑Test : Set _))
    (hSize : Test.card ≤ m + 1)
    (zOutsideCore :
      ↥(↑Test : Set
        (Structure.Attachment.Vertex
          (B.support alpha.toFunctionEmbedding)
          (W := W) (I := PUnit.{v+1}))))
    (hOutsideCore : ¬ ∃ w : W,
      zOutsideCore.1 =
        unitCoreEmbedding B (B.support alpha.toFunctionEmbedding)
          (B.weak_support_closed Douter hB.1 A alpha)
          Dsys f w)
    (zOutsideCopy :
      ↥(↑Test : Set
        (Structure.Attachment.Vertex
          (B.support alpha.toFunctionEmbedding)
          (W := W) (I := PUnit.{v+1}))))
    (hOutsideCopy : ¬ ∃ x : V,
      zOutsideCopy.1 =
        unitCopyEmbedding B (B.support alpha.toFunctionEmbedding)
          (B.weak_support_closed Douter hB.1 A alpha)
          Dsys f x) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.induce (↑Test : Set _) hTest) := by
  classical
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let TestSet : Set
      (Structure.Attachment.Vertex
        Supp (W := W) (I := PUnit.{v+1})) := ↑Test
  let pb := closedTestPullback B Supp hSupp Dsys f TestSet hTest
  letI : Finite pb.Left :=
    Finite.of_injective pb.leftIn pb.leftIn.injective
  letI : Finite pb.Right :=
    Finite.of_injective pb.rightIn pb.rightIn.injective
  letI : Fintype pb.Left := Fintype.ofFinite _
  letI : Fintype pb.Right := Fintype.ofFinite _
  have hSmall := closedMixed_pullback_card_lt B Supp hSupp Dsys f
    Test hTest zOutsideCore hOutsideCore zOutsideCopy hOutsideCopy
  have hLeftSmall : Nat.card pb.Left ≤ m :=
    Nat.lt_succ_iff.mp ((lt_of_lt_of_le hSmall.1 hSize) :
      Nat.card pb.Left < m + 1)
  have hRightSmall : Nat.card pb.Right ≤ m :=
    Nat.lt_succ_iff.mp ((lt_of_lt_of_le hSmall.2.1 hSize) :
      Nat.card pb.Right < m + 1)
  let pL : pb.Left → P := Dsys.part ∘ pb.leftMap
  let pR : pb.Right → P := B.part ∘ pb.rightMap
  have hpL : pb.left.IsEHNHomomorphismEmbedding Douter pL := by
    change pb.left.IsEHNHomomorphismEmbedding Douter
      (Dsys.part ∘ pb.leftMap)
    exact hD.comp pb.leftMap.isEHNHomomorphismEmbedding
  have hpR : pb.right.IsEHNHomomorphismEmbedding Douter pR := by
    change pb.right.IsEHNHomomorphismEmbedding Douter
      (B.part ∘ pb.rightMap)
    exact hB.comp pb.rightMap.isEHNHomomorphismEmbedding
  let q : pb.Common → U :=
    (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
  have hCompat : ∀ x : pb.Common,
      Dsys.part (pb.leftMap (pb.toLeft x)) = alpha (q x) ∧
      B.part (pb.rightMap (pb.toRight x)) = alpha (q x) :=
    closedTestPullback_common_part_compat
      B Douter hB A alpha Dsys f TestSet hTest
  have hRootAgree (x : pb.Common) :
      pL (pb.toLeft x) = pR (pb.toRight x) :=
    (hCompat x).1.trans (hCompat x).2.symm
  have hRootInA (x : pb.Common) :
      ∃ a : U, pL (pb.toLeft x) = alpha a :=
    ⟨q x, (hCompat x).1⟩
  have hCardL : (Finset.univ.image pL).card ≤ m := by
    calc
      (Finset.univ.image pL).card ≤
          (Finset.univ : Finset pb.Left).card :=
        Finset.card_image_le
      _ = Nat.card pb.Left := by
        simp only [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ m := hLeftSmall
  have hCardR : (Finset.univ.image pR).card ≤ m := by
    calc
      (Finset.univ.image pR).card ≤
          (Finset.univ : Finset pb.Right).card :=
        Finset.card_image_le
      _ = Nat.card pb.Right := by
        simp only [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ m := hRightSmall
  exact pb.free.originalPartialTreeCompletion_of_ordinaryControlRank
    Douter alpha pL pR hpL hpR hRootAgree hRootInA
    Base m hPrev hCardL hCardR

end StructuralRamsey.FunctionalPartite.Attachment

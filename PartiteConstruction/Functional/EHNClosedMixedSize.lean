import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-! # Strict size decrease for mixed closed functional EHN tests

The canonical full-function pullback of a closed test into one binary EHN
attachment has two closed sides and a closed common overlap.  If the test
contains a point outside the core and a point outside the attached copy,
then each side is strictly smaller than the entire test; the common part
is smaller still.

This supplies the precise cardinal induction measure for the difficult
reducible-separator case.  No hereditary irreducibility assumption and no
weakly induced subsets are used.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P V W : Type v}
variable (B : System L P V)
variable (S : Set V) (hS : B.toStructure.IsClosed S)
variable (D : System L P W)
variable (f : FunctionalPartite.Embedding (B.induce S hS) D)

/-- A genuinely mixed closed test has a strict cardinal decrease on both
pullback sides and on their common separator.  The witnesses in the
hypotheses are precisely vertices missing from the respective ambient
attachment sides. -/
theorem closedMixed_pullback_card_lt
    (Test : Finset
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B S hS D f).toStructure.IsClosed (↑Test : Set _))
    (zOutsideCore :
      ↥(↑Test : Set
        (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1}))))
    (hOutsideCore : ¬ ∃ w : W,
      zOutsideCore.1 = unitCoreEmbedding B S hS D f w)
    (zOutsideCopy :
      ↥(↑Test : Set
        (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1}))))
    (hOutsideCopy : ¬ ∃ x : V,
      zOutsideCopy.1 = unitCopyEmbedding B S hS D f x) :
    let pb := closedTestPullback B S hS D f (↑Test : Set _) hTest
    Nat.card pb.Left < Test.card ∧
    Nat.card pb.Right < Test.card ∧
    Nat.card pb.Common < Test.card := by
  classical
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  letI : Fintype TestSet := Fintype.ofFinite _
  let pb := closedTestPullback B S hS D f TestSet hTest
  letI : Finite pb.Left :=
    Finite.of_injective pb.leftIn pb.leftIn.injective
  letI : Finite pb.Right :=
    Finite.of_injective pb.rightIn pb.rightIn.injective
  letI : Finite pb.Common :=
    Finite.of_injective pb.toLeft pb.toLeft.injective
  letI : Fintype pb.Left := Fintype.ofFinite _
  letI : Fintype pb.Right := Fintype.ofFinite _
  letI : Fintype pb.Common := Fintype.ofFinite _

  have hnotL : ¬ Function.Surjective pb.leftIn := by
    intro hsurj
    obtain ⟨a, ha⟩ := hsurj zOutsideCore
    apply hOutsideCore
    refine ⟨pb.leftMap a, ?_⟩
    calc
      zOutsideCore.1 = (pb.leftIn a).1 :=
        congrArg Subtype.val ha.symm
      _ = unitCoreEmbedding B S hS D f (pb.leftMap a) :=
        pb.left_factor a

  have hnotR : ¬ Function.Surjective pb.rightIn := by
    intro hsurj
    obtain ⟨b, hb⟩ := hsurj zOutsideCopy
    apply hOutsideCopy
    refine ⟨pb.rightMap b, ?_⟩
    calc
      zOutsideCopy.1 = (pb.rightIn b).1 :=
        congrArg Subtype.val hb.symm
      _ = unitCopyEmbedding B S hS D f (pb.rightMap b) :=
        pb.right_factor b

  have hleft : Nat.card pb.Left < Test.card := by
    rw [Nat.card_eq_fintype_card]
    have hlt : Fintype.card pb.Left < Fintype.card TestSet :=
      Fintype.card_lt_of_injective_not_surjective
        pb.leftIn pb.leftIn.injective hnotL
    simpa [TestSet] using hlt

  have hright : Nat.card pb.Right < Test.card := by
    rw [Nat.card_eq_fintype_card]
    have hlt : Fintype.card pb.Right < Fintype.card TestSet :=
      Fintype.card_lt_of_injective_not_surjective
        pb.rightIn pb.rightIn.injective hnotR
    simpa [TestSet] using hlt

  have hcommon : Nat.card pb.Common < Test.card := by
    have hle :
        Fintype.card pb.Common ≤ Fintype.card pb.Left :=
      Fintype.card_le_of_injective pb.toLeft pb.toLeft.injective
    calc
      Nat.card pb.Common = Fintype.card pb.Common :=
        Nat.card_eq_fintype_card
      _ ≤ Fintype.card pb.Left := hle
      _ < Test.card := by
        simpa only [Nat.card_eq_fintype_card] using hleft

  exact ⟨hleft, hright, hcommon⟩

end StructuralRamsey.FunctionalPartite.Attachment

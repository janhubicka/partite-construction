import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.FreeAmalgamClosedInduce

/-! # Closed-test decomposition for one binary EHN attachment

A binary EHN attachment is a full free amalgam of its core and one copied
stage over a closed support.  Restricting to a closed finite test therefore
gives a full free-amalgam decomposition into the closed core and copy
preimages.

If the test is genuinely mixed (not contained in either side), both side
preimages are strictly smaller.  This is the finite induction skeleton for
the functional mixed Picture step.
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

noncomputable abbrev UnitAttachD :=
  attach B S hS D (fun _ : PUnit.{v+1} => f)

noncomputable abbrev unitCoreEmbedding :
    Structure.Embedding D.toStructure (UnitAttachD B S hS D f).toStructure :=
  Structure.Attachment.coreEmbedding
    B.toStructure S hS D.toStructure
    (fun _ : PUnit.{v+1} => f.toEmbedding)

noncomputable abbrev unitCopyEmbedding :
    Structure.Embedding B.toStructure (UnitAttachD B S hS D f).toStructure :=
  Structure.Attachment.copyEmbedding
    B.toStructure S hS D.toStructure
    (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit

theorem unit_isFreeAmalgam_full :
    Structure.IsFreeAmalgam
      f.toEmbedding
      (Structure.inclusion B.toStructure S hS)
      (unitCoreEmbedding B S hS D f)
      (unitCopyEmbedding B S hS D f) :=
  Structure.Attachment.unit_isFreeAmalgam
    B.toStructure S hS D.toStructure f.toEmbedding

/-- A closed test inherits the canonical full free-amalgam decomposition of
the binary attachment. -/
theorem closedTest_decompose
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test) :
    let coreSet : Set W :=
      (unitCoreEmbedding B S hS D f) ⁻¹' Test
    let copySet : Set V :=
      (unitCopyEmbedding B S hS D f) ⁻¹' Test
    let rootSet : Set S :=
      ((unitCoreEmbedding B S hS D f).comp f.toEmbedding) ⁻¹' Test
    let hCore :
      D.toStructure.IsClosed coreSet :=
      (unitCoreEmbedding B S hS D f).preimage_isClosed Test hTest
    let hCopy :
      B.toStructure.IsClosed copySet :=
      (unitCopyEmbedding B S hS D f).preimage_isClosed Test hTest
    let hRoot :
      (B.induce S hS).toStructure.IsClosed rootSet :=
      ((unitCoreEmbedding B S hS D f).comp f.toEmbedding).
        preimage_isClosed Test hTest
    let CoreSmall := D.toStructure.induce coreSet hCore
    let CopySmall := B.toStructure.induce copySet hCopy
    let RootSmall := (B.induce S hS).toStructure.induce rootSet hRoot
    let WholeSmall :=
      (UnitAttachD B S hS D f).toStructure.induce Test hTest
    ∃ (mCore : Structure.Embedding RootSmall CoreSmall)
      (mCopy : Structure.Embedding RootSmall CopySmall)
      (jCore : Structure.Embedding CoreSmall WholeSmall)
      (jCopy : Structure.Embedding CopySmall WholeSmall),
      Structure.IsFreeAmalgam mCore mCopy jCore jCopy := by
  simpa [unitCoreEmbedding, unitCopyEmbedding, UnitAttachD] using
    (unit_isFreeAmalgam_full B S hS D f).induceClosed Test hTest

/-- In a genuinely mixed finite test, the core preimage is strictly smaller. -/
theorem corePreimage_card_lt
    (Test : Finset (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (z : ↥(↑Test : Set _))
    (hz : ¬ ∃ w : W,
      z.1 = unitCoreEmbedding B S hS D f w) :
    Fintype.card
        ((unitCoreEmbedding B S hS D f) ⁻¹'
          (↑Test : Set _)) <
      Test.card := by
  classical
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  letI : Fintype TestSet := Fintype.ofFinite _
  let CoreSet : Set W :=
    (unitCoreEmbedding B S hS D f) ⁻¹' TestSet
  letI : Fintype CoreSet := Fintype.ofFinite _
  have hlt :
      Fintype.card CoreSet < Fintype.card TestSet :=
    (unit_isFreeAmalgam_full B S hS D f).leftPreimage_card_lt
      TestSet hTest z hz
  simpa [CoreSet, TestSet] using hlt

/-- Symmetrically, a point outside the copied side makes the copy preimage
strictly smaller. -/
theorem copyPreimage_card_lt
    (Test : Finset (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (z : ↥(↑Test : Set _))
    (hz : ¬ ∃ x : V,
      z.1 = unitCopyEmbedding B S hS D f x) :
    Fintype.card
        ((unitCopyEmbedding B S hS D f) ⁻¹'
          (↑Test : Set _)) <
      Test.card := by
  classical
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  letI : Fintype TestSet := Fintype.ofFinite _
  let CopySet : Set V :=
    (unitCopyEmbedding B S hS D f) ⁻¹' TestSet
  letI : Fintype CopySet := Fintype.ofFinite _
  have hlt :
      Fintype.card CopySet < Fintype.card TestSet :=
    (unit_isFreeAmalgam_full B S hS D f).rightPreimage_card_lt
      TestSet hTest z hz
  simpa [CopySet, TestSet] using hlt

end StructuralRamsey.FunctionalPartite.Attachment

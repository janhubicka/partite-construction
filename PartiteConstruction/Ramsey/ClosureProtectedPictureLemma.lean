import PartiteConstruction.Ramsey.ClosurePowerProtected

/-! # The protected native Ramsey Picture lemma

The formerly separate positive-power protection premise is now discharged
by ClosurePowerProtected. The result constructs the actual finite
all-embeddings Picture witness with Ramsey, closedness, protected
projection and protected-test coverage conclusions together.

The rank-increment completion argument is not part of this theorem.
The working closed-test convention is not the literal nonclosed-test
convention of published Definition 2.15.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v}

/-- The complete local protected Ramsey Picture step, with no assumed
protection theorem for powers and no irreducible-generator shortcut. -/
theorem pictureLemma_protected
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure D B.part)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite Q] [Finite V]
    (Color : Type*) [Fintype Color] :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      PictureProperty A B alpha.toFunctionEmbedding C Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  have hSupport : IsUSubstructure rules B.toRelStructure
      (B.support alpha.toFunctionEmbedding) :=
    (alpha.range_isUSubstructure hA hD).preimage_homomorphism hBPart.1
  have hRestrictedClosed : IsUClosed rules
      (B.restrict alpha.toFunctionEmbedding).toRelStructure :=
    hB.induce_of_USubstructure (B.support alpha.toFunctionEmbedding) hSupport
  apply pictureLemma_protected_of_power A D B alpha hA hD hB hBPart aB Color
  intro N hN
  exact power_part_protected (B.restrict alpha.toFunctionEmbedding)
    hRestrictedClosed (restrict_isClosedPartiteOver A D B alpha hBPart) hN

end StructuralRamsey.Partite.Induced

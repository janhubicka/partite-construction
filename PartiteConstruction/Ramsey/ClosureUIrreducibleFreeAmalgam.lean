import PartiteConstruction.Iterated.WeakFreeAmalgamInduce
import PartiteConstruction.Ramsey.ClosureUIrreducible2019
import PartiteConstruction.Ramsey.ClosureUSubstructurePreimage

/-! # U-irreducible tests inside weak free amalgams (2019)

An arbitrary vertex restriction of a free amalgam is itself a free
amalgam of the exact inverse-image tests.  If the original test is a
U-substructure, and the original sides are U-closed, then the induced
side tests are U-closed too.  Therefore a U-irreducible tested
substructure must lie in one side.

The common root need not be U-closed for this localization theorem:
the definition of U-irreducibility only requires the two decomposing
sides to be U-closed.  This is NOT a tree-completion theorem.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Exact side localization for U-irreducible U-substructure tests
in a free amalgam of U-closed sides.  Neither the weak test nor the
side preimages are enlarged to generated closures. -/
theorem IsFreeAmalgam.uIrreducible_side
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (S : Set C)
    (hS : IsUSubstructure rules Whole S)
    (hIrred : IsUIrreducible rules (Whole.induce S)) :
    (∀ z : S, ∃ a : E, z.1 = iL a) ∨
    (∀ z : S, ∃ b : F, z.1 = iR b) := by
  classical
  let Lset : Set E := iL ⁻¹' S
  let Rset : Set F := iR ⁻¹' S
  have hLS : IsUClosed rules (Left.induce Lset) :=
    hLeft.induce_preimage_embedding hS iL
  have hRS : IsUClosed rules (Right.induce Rset) :=
    hRight.induce_preimage_embedding hS iR
  obtain ⟨mL, mR, jL, jR, hRestricted, hjL, hjR⟩ :=
    hFree.weakInduce_withMaps S
  rcases hIrred hLS hRS hRestricted with hSurjL | hSurjR
  · left
    intro z
    obtain ⟨a, ha⟩ := hSurjL z
    exact ⟨a.1, (congrArg Subtype.val ha).symm.trans (hjL a)⟩
  · right
    intro z
    obtain ⟨b, hb⟩ := hSurjR z
    exact ⟨b.1, (congrArg Subtype.val hb).symm.trans (hjR b)⟩

/-- If a U-substructure test meets both exclusive sides of a free
amalgam with U-closed sides, it cannot be U-irreducible. -/
theorem IsFreeAmalgam.mixed_not_uIrreducible
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (S : Set C)
    (hS : IsUSubstructure rules Whole S)
    (zLeft : S) (hzLeft : ¬ ∃ a : E, zLeft.1 = iL a)
    (zRight : S) (hzRight : ¬ ∃ b : F, zRight.1 = iR b) :
    ¬ IsUIrreducible rules (Whole.induce S) := by
  intro hIrred
  rcases hFree.uIrreducible_side hLeft hRight S hS hIrred with
      hOnLeft | hOnRight
  · exact hzLeft (hOnLeft zLeft)
  · exact hzRight (hOnRight zRight)

end StructuralRamsey.RelStructure

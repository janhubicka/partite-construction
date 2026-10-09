import PartiteConstruction.Ramsey.ClosureFreeAmalgamGenerators

/-! # The valid two-sided generator drop is relative to the common root

The absolute side ranks of a free amalgam can equal the whole rank.
What the free source geometry does imply is smaller generating supports
AFTER the entire common root is supplied. This module proves that exact
statement; it introduces no relative-completion oracle and does not claim
that the root's generators cost nothing in the existing absolute invariant.

The drop is derived from finite generator sets of the WHOLE source. It is
not inferred from the total number of vertices in either side.
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

/-- A generator outside the left side gives a strictly smaller left
support, once the full common root is added to that support. -/
theorem IsFreeAmalgam.left_generator_drop_over_root
    [Finite E]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L)
    (G : Finset C) (hGen : IsUGenerating rules Whole (↑G : Set C))
    (z : C) (hz : z ∈ G) (hOutside : z ∉ Set.range iL) :
    ∃ S : Finset E, S.card < G.card ∧
      IsUGenerating rules Left ((↑S : Set E) ∪ Set.range sL) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let S : Finset E := Finset.univ.filter (fun a => iL a ∈ G)
  have hImage : S.image iL ⊆ G.erase z := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact hOutside ⟨a, he⟩
    · exact (Finset.mem_filter.mp ha).2
  have hBound : S.card ≤ (G.erase z).card := by
    calc
      S.card = (S.image iL).card :=
        (Finset.card_image_of_injective S iL.injective).symm
      _ ≤ (G.erase z).card := Finset.card_le_card hImage
  have hErase := Finset.card_erase_of_mem hz
  have hPositive : 0 < G.card := Finset.card_pos.mpr ⟨z, hz⟩
  have hSmall : S.card < G.card := by omega
  have hSet : (↑S : Set E) = iL ⁻¹' (↑G : Set C) := by
    ext a
    simp [S]
  refine ⟨S, hSmall, ?_⟩
  rw [hSet]
  exact hFree.left_generated_over_root rules (↑G : Set C) hGen

/-- Symmetric relative generator drop. -/
theorem IsFreeAmalgam.right_generator_drop_over_root
    [Finite F]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L)
    (G : Finset C) (hGen : IsUGenerating rules Whole (↑G : Set C))
    (z : C) (hz : z ∈ G) (hOutside : z ∉ Set.range iR) :
    ∃ S : Finset F, S.card < G.card ∧
      IsUGenerating rules Right ((↑S : Set F) ∪ Set.range sR) :=
  hFree.swap.left_generator_drop_over_root rules G hGen z hz hOutside

/-- If generators occur on both exclusive sides and there are at most
j+1 of them, both sides have at most j additional generators OVER their
common root. This is not an absolute U-size bound on the two sides. -/
theorem IsFreeAmalgam.both_generator_budgets_over_root
    [Finite E] [Finite F]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L)
    (G : Finset C) (hGen : IsUGenerating rules Whole (↑G : Set C))
    (j : ℕ) (hCard : G.card ≤ j + 1)
    (zL zR : C) (hzL : zL ∈ G) (hzR : zR ∈ G)
    (hOutsideLeft : zL ∉ Set.range iL)
    (hOutsideRight : zR ∉ Set.range iR) :
    ∃ (SLeft : Finset E) (SRight : Finset F),
      SLeft.card ≤ j ∧ SRight.card ≤ j ∧
      IsUGenerating rules Left ((↑SLeft : Set E) ∪ Set.range sL) ∧
      IsUGenerating rules Right ((↑SRight : Set F) ∪ Set.range sR) := by
  obtain ⟨SLeft, hLeft, hGenLeft⟩ :=
    hFree.left_generator_drop_over_root rules G hGen zL hzL hOutsideLeft
  obtain ⟨SRight, hRight, hGenRight⟩ :=
    hFree.right_generator_drop_over_root rules G hGen zR hzR hOutsideRight
  refine ⟨SLeft, SRight, ?_, ?_, hGenLeft, hGenRight⟩ <;> omega

end StructuralRamsey.RelStructure

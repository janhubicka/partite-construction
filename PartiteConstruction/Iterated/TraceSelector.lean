import PartiteConstruction.Relational.Basic

/-! # Finite trace representatives

For a finite family of objects, one can choose one representative for each
labelled trace on a finite test.  We retain only the indices of these
representatives, together with an arbitrary prescribed active set.

This is the finite counting component of the uniform final-attachment proof.
The intended trace type is `A → Option Test`: for each labelled vertex of an
ambient A-copy, record the tested vertex when it belongs to the current test
and `none` otherwise.
-/
namespace StructuralRamsey.FiniteTrace

universe u v w

variable {A I T X : Type*}

/-- Choose the active indices and one index for every realized trace. -/
theorem selectIndices
    [Fintype A] [Fintype I] [Fintype T] [Fintype X]
    [DecidableEq I] [DecidableEq (A → Option T)]
    (idx : X → I)
    (trace : X → A → Option T)
    (active : Finset I) :
    ∃ J : Finset I,
      active ⊆ J ∧
      J.card ≤ active.card + (Fintype.card T + 1) ^ Fintype.card A ∧
      ∀ x : X, ∃ y : X, idx y ∈ J ∧ trace y = trace x := by
  classical
  let TraceSpace := A → Option T
  let realized : Finset TraceSpace := Finset.univ.image trace
  let Realized := {τ : TraceSpace // τ ∈ realized}
  let pick : Realized → X := fun τ =>
    Classical.choose (by
      rcases Finset.mem_image.mp τ.2 with ⟨x, _, hx⟩
      exact ⟨x, hx⟩)
  have hpick (τ : Realized) : trace (pick τ) = τ.1 := by
    exact Classical.choose_spec (by
      rcases Finset.mem_image.mp τ.2 with ⟨x, _, hx⟩
      exact ⟨x, hx⟩)
  let pickedIndices : Finset I :=
    Finset.univ.image (fun τ : Realized => idx (pick τ))
  let J := active ∪ pickedIndices
  refine ⟨J, Finset.subset_union_left, ?_, ?_⟩
  · calc
      J.card ≤ active.card + pickedIndices.card :=
        Finset.card_union_le _ _
      _ ≤ active.card + Fintype.card Realized := by
        exact Nat.add_le_add_left Finset.card_image_le active.card
      _ ≤ active.card + Fintype.card TraceSpace := by
        apply Nat.add_le_add_left
        exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = active.card + (Fintype.card T + 1) ^ Fintype.card A := by
        simp [TraceSpace, Fintype.card_congr (Equiv.refl (Option T))]
  · intro x
    have hmem : trace x ∈ realized := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    let τ : Realized := ⟨trace x, hmem⟩
    refine ⟨pick τ, ?_, ?_⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨τ, Finset.mem_univ τ, rfl⟩
    · exact hpick τ

/-- Cruder cardinal form useful when only a bound on the active set and test
size is available. -/
theorem selectIndices_cardBound
    [Fintype A] [Fintype I] [Fintype T] [Fintype X]
    [DecidableEq I] [DecidableEq (A → Option T)]
    (idx : X → I)
    (trace : X → A → Option T)
    (active : Finset I)
    (n : ℕ)
    (hactive : active.card ≤ n)
    (hT : Fintype.card T ≤ n) :
    ∃ J : Finset I,
      active ⊆ J ∧
      J.card ≤ n + (n + 1) ^ Fintype.card A ∧
      ∀ x : X, ∃ y : X, idx y ∈ J ∧ trace y = trace x := by
  obtain ⟨J, hsub, hcard, hrep⟩ :=
    selectIndices idx trace active
  refine ⟨J, hsub, ?_, hrep⟩
  calc
    J.card ≤ active.card + (Fintype.card T + 1) ^ Fintype.card A := hcard
    _ ≤ n + (n + 1) ^ Fintype.card A := by
      apply Nat.add_le_add hactive
      exact Nat.pow_le_pow_left (Nat.add_le_add_right hT 1) _

end StructuralRamsey.FiniteTrace

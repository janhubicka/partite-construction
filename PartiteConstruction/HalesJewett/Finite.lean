import SuccessorTree.HalesJewett.AlphabetInduction

/-! # Fixed-length Hales--Jewett from the verified starred theorem

If every length had a bad colouring, their disjoint union would colour all
finite words badly. The imported starred theorem rules this out. Thus the
length is chosen before the colouring, as required for a finite Ramsey witness.
-/
namespace StructuralRamsey.HalesJewett

open SuccessorTree

universe u v

structure Line (α : Type u) (N : ℕ) where
  symbol : Fin N → LineSymbol α
  hasParameter : ∃ i, symbol i = .parameter

namespace Line

def eval (W : Line α N) (a : α) : Fin N → α :=
  fun i => (W.symbol i).eval a

theorem length_pos (W : Line α N) : 0 < N := by
  obtain ⟨i, _⟩ := W.hasParameter
  exact Nat.zero_lt_of_lt i.isLt

end Line

/-- All finite colour sets, including the empty colour set; no HJ axiom is assumed. -/
theorem finite {α : Type u} {κ : Type v} [Fintype α] [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ ∀ χ : (Fin N → α) → κ,
      ∃ W : Line α N, ∀ a b, χ (W.eval a) = χ (W.eval b) := by
  classical
  by_contra h
  have bad : ∀ N : ℕ, ∃ χ : (Fin N → α) → κ,
      ∀ W : Line α N, ¬ (∀ a b, χ (W.eval a) = χ (W.eval b)) := by
    intro N
    by_cases hn : 0 < N
    · have hN : ¬ ∀ χ : (Fin N → α) → κ,
          ∃ W : Line α N, ∀ a b, χ (W.eval a) = χ (W.eval b) :=
        fun hgood => h ⟨N, hn, hgood⟩
      push Not at hN ⊢
      exact hN
    · have hκ : Nonempty κ := by
        by_contra he
        have : IsEmpty κ := not_nonempty_iff.mp he
        apply h
        refine ⟨1, by omega, ?_⟩
        intro χ
        by_cases ha : Nonempty α
        · exact isEmptyElim (χ (fun _ => Classical.choice ha))
        · have : IsEmpty α := not_nonempty_iff.mp ha
          exact ⟨⟨fun _ => .parameter, ⟨0, rfl⟩⟩, fun a => isEmptyElim a⟩
      refine ⟨fun _ => Classical.choice hκ, ?_⟩
      intro W
      exact (hn W.length_pos).elim
  choose χ hχ using bad
  let colour : List α → κ := fun w => χ w.length w.get
  obtain ⟨W, hW⟩ := SuccessorTree.HalesJewett.starHJ_finite colour
  let L : Line α W.word.length :=
    ⟨W.word.get, by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp W.hasParameter
      exact ⟨i, hi⟩⟩
  apply hχ W.word.length L
  intro a b
  have hc (a : α) : colour (W.eval a) = χ W.word.length (L.eval a) := by
    dsimp only [colour, StarLine.eval, evalWord, L, Line.eval]
    congr 1
    · simp
    · apply (Fin.heq_fun_iff (List.length_map ..)).mpr
      intro i
      simp [List.get_eq_getElem, Line.eval]
  rw [← hc a, ← hc b]
  exact (hW a).trans (hW b).symm

end StructuralRamsey.HalesJewett

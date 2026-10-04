import PartiteConstruction.Structure.RootedFunctor

set_option autoImplicit false

/-! # Splitting a structure into its fixed root and moving part -/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R U : Type v} {n : ℕ}

/-- Reattach the root at the level of carriers. -/
def unsplit
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :
    Sum R (Outside ρ) → U
  | .inl r => ρ r
  | .inr x => x.1

/-- Split a vertex into its root coordinate when it lies in the root, and
otherwise into the moving complement. -/
noncomputable def split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :
    U → Sum R (Outside ρ) := by
  classical
  exact fun a =>
    if h : a ∈ Set.range ρ then
      Sum.inl (Classical.choose h)
    else
      Sum.inr ⟨a, h⟩

@[simp] theorem unsplit_split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (a : U) :
    unsplit ρ (split ρ a) = a := by
  classical
  by_cases h : a ∈ Set.range ρ
  · simp only [split, dif_pos h, unsplit]
    exact Classical.choose_spec h
  · simp [split, h, unsplit]

@[simp] theorem split_unsplit
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (x : Sum R (Outside ρ)) :
    split ρ (unsplit ρ x) = x := by
  classical
  cases x with
  | inl r =>
      have h : ρ r ∈ Set.range ρ := ⟨r, rfl⟩
      simp only [unsplit, split, dif_pos h]
      apply congrArg Sum.inl
      exact ρ.injective (Classical.choose_spec h)
  | inr x =>
      have h : x.1 ∉ Set.range ρ := x.2
      simp [unsplit, split, h]

noncomputable def splitEquiv
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :
    U ≃ Sum R (Outside ρ) where
  toFun := split ρ
  invFun := unsplit ρ
  left_inv := unsplit_split ρ
  right_inv := split_unsplit ρ

theorem unsplit_sumFill
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A)
    (p : Pattern n R) (x : Fin n → Outside ρ) :
    unsplit ρ ∘ Pattern.sumFill p x =
      Pattern.fill ρ p x := by
  funext i
  cases h : p.fixed i with
  | some r => simp [Pattern.sumFill, Pattern.fill, unsplit, h]
  | none => simp [Pattern.sumFill, Pattern.fill, unsplit, h]

/-- Decoding the encoded arguments recovers the original tuple whenever at
least one coordinate is moving. -/
theorem fill_pad_split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A)
    (x : Fin n → U)
    (h : (Pattern.ofTuple (split ρ ∘ x)).HasMoving) :
    Pattern.fill ρ (Pattern.ofTuple (split ρ ∘ x))
        (Pattern.pad (split ρ ∘ x) h) = x := by
  calc
    Pattern.fill ρ (Pattern.ofTuple (split ρ ∘ x))
        (Pattern.pad (split ρ ∘ x) h) =
      unsplit ρ ∘
        Pattern.sumFill (Pattern.ofTuple (split ρ ∘ x))
          (Pattern.pad (split ρ ∘ x) h) := by
            symm
            exact unsplit_sumFill ρ _ _
    _ = unsplit ρ ∘ (split ρ ∘ x) := by
          rw [Pattern.sumFill_ofTuple_pad]
    _ = x := by
          funext i
          exact unsplit_split ρ (x i)

/-- If all split coordinates lie in the root, the root tuple also recovers
the original tuple. -/
theorem rootTuple_split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A)
    (x : Fin n → U)
    (h : ¬(Pattern.ofTuple (split ρ ∘ x)).HasMoving) :
    ρ ∘ Pattern.rootTuple (split ρ ∘ x) h = x := by
  have hs := Pattern.inl_rootTuple (split ρ ∘ x) h
  funext i
  have hi := congrFun hs i
  have hu := congrArg (unsplit ρ) hi
  simpa [Function.comp_apply, unsplit] using hu

end StructuralRamsey.Rooted

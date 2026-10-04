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

/-- Chosen root preimage of a vertex known to lie in the root range. -/
noncomputable def rootPreimage
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) {a : U}
    (h : a ∈ Set.range ρ) : R :=
  Classical.choose (show ∃ r, ρ r = a from h)

theorem rootPreimage_spec
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) {a : U}
    (h : a ∈ Set.range ρ) :
    ρ (rootPreimage ρ h) = a :=
  Classical.choose_spec (show ∃ r, ρ r = a from h)

/-- Split a vertex into its root coordinate when it lies in the root, and
otherwise into the moving complement. -/
noncomputable def split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (a : U) :
    Sum R (Outside ρ) :=
  letI : Decidable (a ∈ Set.range ρ) := Classical.propDecidable _
  if h : a ∈ Set.range ρ then
    Sum.inl (rootPreimage ρ h)
  else
    Sum.inr ⟨a, h⟩

@[simp] theorem unsplit_split
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (a : U) :
    unsplit ρ (split ρ a) = a := by
  classical
  by_cases h : a ∈ Set.range ρ
  · unfold split
    rw [dite_eq_left h]
    exact rootPreimage_spec ρ h
  · unfold split
    rw [dite_eq_right h]
    rfl

theorem unsplit_injective
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :
    Function.Injective (unsplit ρ) := by
  intro x y hxy
  cases x with
  | inl r =>
      cases y with
      | inl s =>
          apply congrArg Sum.inl
          exact ρ.injective hxy
      | inr y =>
          change ρ r = y.1 at hxy
          exact False.elim (y.2 ⟨r, hxy⟩)
  | inr x =>
      cases y with
      | inl s =>
          change x.1 = ρ s at hxy
          exact False.elim (x.2 ⟨s, hxy.symm⟩)
      | inr y =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hxy

@[simp] theorem split_unsplit
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (x : Sum R (Outside ρ)) :
    split ρ (unsplit ρ x) = x := by
  apply unsplit_injective ρ
  rw [unsplit_split]


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
  change ρ (Pattern.rootTuple (split ρ ∘ x) h i) =
    unsplit ρ (split ρ (x i)) at hu
  rw [unsplit_split] at hu
  exact hu

end StructuralRamsey.Rooted

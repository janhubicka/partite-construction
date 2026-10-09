import PartiteConstruction.Ramsey.CompletionTransfer

/-! # Ramsey transfer needs preservation of B-copies only

For the last step of Theorem 2.18, a single vertex map preserving every
B-copy suffices. No irreducibility assumption on A or B and no coverage
of arbitrary A-copies by B-copies is needed.

Given a colouring in the completed target, pull it back on A-copies
whose composite vertex maps are embeddings. Give all remaining A-copies
an arbitrary default colour. Every A-copy inside the monochromatic
B-copy is in the first case, since that whole B-copy is preserved.

This proves exactly the colouring implication of Definition 2.16,
independently of any choice of U-irreducibility semantics. It does not
construct the completion map or discharge local finiteness.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- A B-copywise completion transfers a Ramsey arrow. The completion
map can fail to preserve A-copies outside B-copies; they receive a
fallback colour which is never used in the final comparison. -/
theorem arrow_of_BCopywiseCompletion
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {D : RelStructure L X}
    {f : W → X} {κ : Type*} [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C κ)
    (hB : CopywiseCompletion B C D f) :
    StructuralRamsey.Arrow A B D κ := by
  classical
  intro χ
  let liftable (a : Embedding A C) : Prop :=
    ∃ d : Embedding A D, ∀ x : U, d x = f (a x)
  let pullColour (a : Embedding A C) : κ :=
    if h : liftable a then χ (Classical.choose h)
    else Classical.choice (inferInstance : Nonempty κ)
  have pull_spec (a : Embedding A C) (d : Embedding A D)
      (hd : ∀ x : U, d x = f (a x)) :
      pullColour a = χ d := by
    have ha : liftable a := ⟨d, hd⟩
    have hEq : Classical.choose ha = d := by
      apply Embedding.ext
      intro x
      exact (Classical.choose_spec ha x).trans (hd x).symm
    change (if h : liftable a then χ (Classical.choose h)
      else Classical.choice (inferInstance : Nonempty κ)) = χ d
    rw [dif_pos ha, hEq]
  obtain ⟨b, hMono⟩ := hArrow pullColour
  obtain ⟨bD, hbD⟩ := hB b
  have hPull (e : Embedding A B) :
      pullColour (b.comp e) = χ (bD.comp e) := by
    apply pull_spec
    intro x
    exact hbD (e x)
  refine ⟨bD, ?_⟩
  intro e₁ e₂
  calc
    χ (bD.comp e₁) = pullColour (b.comp e₁) := (hPull e₁).symm
    _ = pullColour (b.comp e₂) := hMono e₁ e₂
    _ = χ (bD.comp e₂) := hPull e₂

/-- Class-valued version of the final colouring step. All structural
conditions belong to the construction of `hCompletion`, not here. -/
theorem arrow_of_BCopywiseCompletion_inClass
    {K : StructureClass.{u,v} (L := L)}
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {κ : Type*} [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C κ)
    (hCompletion : HasCopywiseCompletion K B C) :
    ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
      K D ∧ StructuralRamsey.Arrow A B D κ := by
  obtain ⟨X, hX, D, hKD, f, hf⟩ := hCompletion
  exact ⟨X, hX, D, hKD, arrow_of_BCopywiseCompletion hArrow hf⟩

end StructuralRamsey.RelStructure

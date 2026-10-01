import PartiteConstruction.Relational.Basic

/-! # The embedding formulation of structural Ramsey arrows -/
namespace StructuralRamsey

open RelStructure

variable {L : RelLanguage} {V W X Y : Type*}
variable {A : RelStructure L V} {B : RelStructure L W}
variable {C : RelStructure L X} {D : RelStructure L Y} {κ : Type*}

/-- Pairwise constancy also gives the intended vacuous meaning for no copies. -/
def Monochromatic (χ : Embedding A C → κ) (f : Embedding B C) : Prop :=
  ∀ e₁ e₂ : Embedding A B, χ (f.comp e₁) = χ (f.comp e₂)

def Arrow (A : RelStructure L V) (B : RelStructure L W)
    (C : RelStructure L X) (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C, Monochromatic χ f

/-- Ramsey arrows are preserved by embedding the witness into a larger structure. -/
theorem Arrow.of_embedding (h : Arrow A B C κ) (g : Embedding C D) :
    Arrow A B D κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ (g.comp e))
  refine ⟨g.comp f, ?_⟩
  intro e₁ e₂
  simpa only [Embedding.comp_assoc] using hf e₁ e₂

/-- No A-copy in B makes the arrow to B itself vacuous. -/
theorem arrow_of_isEmpty [IsEmpty (Embedding A B)] : Arrow A B B κ := by
  intro χ
  exact ⟨Embedding.id B, fun e _ => isEmptyElim e⟩

end StructuralRamsey

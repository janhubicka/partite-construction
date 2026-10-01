import PartiteConstruction.Partite.Basic

/-! # Unary-predicate interface

This checks the link between partition maps and the survey's expanded
language L_P. An induced embedding of expansions is exactly a part-preserving
induced embedding of the base structures.
-/
namespace StructuralRamsey.Partite

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {U : Type z}

def expandedLanguage (L : RelLanguage.{u}) (P : Type v) : RelLanguage where
  Symbol := L.Symbol ⊕ P
  arity := Sum.elim L.arity (fun _ => 1)

def System.expand (A : System L P V) : RelStructure (expandedLanguage L P) V where
  rel
    | .inl R, x => A.rel R x
    | .inr p, x => A.part (x ⟨0, Nat.zero_lt_one⟩) = p

namespace Embedding

variable {A : System L P V} {B : System L P U}

def expand (f : Embedding A B) : RelStructure.Embedding A.expand B.expand where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact f.map_rel_iff R x
    | inr p =>
        change (B.part (f (x (0 : Fin 1))) = p) ↔ (A.part (x (0 : Fin 1)) = p)
        rw [f.map_part]

def ofExpanded (f : RelStructure.Embedding A.expand B.expand) : Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff R x := f.map_rel_iff (.inl R) x
  map_part x := (f.map_rel_iff (.inr (A.part x)) (fun _ => x)).mpr rfl

/-- Exact equivalence, not just preservation in one direction. -/
def expandedEquiv : Embedding A B ≃ RelStructure.Embedding A.expand B.expand where
  toFun := expand
  invFun := ofExpanded
  left_inv := fun _ => by ext; rfl
  right_inv := fun _ => by ext; rfl

@[simp] theorem expand_comp {X : Type*} {C : System L P X}
    (g : Embedding B C) (f : Embedding A B) :
    (g.comp f).expand = g.expand.comp f.expand := rfl

end Embedding

/-- The partite arrow is exactly the ordinary structural arrow in L_P. -/
theorem arrow_iff_expanded {A : System L P V} {B : System L P U}
    {X : Type*} {C : System L P X} {κ : Type*} :
    Partite.Arrow A B C κ ↔ StructuralRamsey.Arrow A.expand B.expand C.expand κ := by
  constructor
  · intro h χ
    obtain ⟨f, hf⟩ := h (fun e => χ e.expand)
    refine ⟨f.expand, ?_⟩
    intro e₁ e₂
    exact hf (Embedding.ofExpanded e₁) (Embedding.ofExpanded e₂)
  · intro h χ
    obtain ⟨f, hf⟩ := h (fun e => χ (Embedding.ofExpanded e))
    refine ⟨Embedding.ofExpanded f, ?_⟩
    intro e₁ e₂
    exact hf e₁.expand e₂.expand

end StructuralRamsey.Partite

import PartiteConstruction.Partite.Initial
import PartiteConstruction.Partite.Invariants

/-! # The non-induced construction from a Ramsey family of projections

The combinatorial input is explicit: a finite family of placements of B into
the part set must be Ramsey for the projections of A-copies. For ordered
structures this input is the ordinary finite subset Ramsey theorem.

The theorem below performs the entire structural part of the argument:
initial picture, finite iteration, extension of the colouring to unrealized
projections, and extraction of an induced monochromatic B-copy. Constraints
on projected relation tuples are retained for later order completion.
-/
namespace StructuralRamsey.Partite

universe u v
variable {L : RelLanguage.{u}} {U V P I : Type v}
variable (A : RelStructure L U) (B : RelStructure L V) (β : I → V ↪ P)

def copyProjection (i : I) (e : RelStructure.Embedding A B) : U ↪ P where
  toFun x := β i (e x)
  inj' := (β i).injective.comp e.injective

/-- Ramsey input on placements, independent of any partite construction. -/
def ProjectionRamsey (κ : Type*) : Prop :=
  ∀ θ : (U ↪ P) → κ, ∃ i : I,
    ∀ e₁ e₂ : RelStructure.Embedding A B,
      θ (copyProjection A B β i e₁) = θ (copyProjection A B β i e₂)

def initialProjectedCopy (i : I) (e : RelStructure.Embedding A B) :
    ProjectedEmbedding A (Initial.picture B β) (copyProjection A B β i e) :=
  ⟨(Initial.copyEmbedding B β i).comp e, fun _ => rfl⟩

/-- Finite non-induced partite construction, including the final Ramsey
reduction. The finite Ramsey property of the placements is an input hypothesis,
not a postulated axiom or an implicit assumption of the conclusion. -/
theorem ramseyFromProjections [Finite U] [Finite V] [Finite P] [Finite I]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : ProjectionRamsey A B β κ)
    (Q : (R : L.Symbol) → (Fin (L.arity R) → P) → Prop)
    (hQ : ∀ i R x, B.rel R x → Q R (β i ∘ x)) :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      C.Respects Q ∧ StructuralRamsey.Arrow A B C.toRelStructure κ := by
  classical
  let : Fintype (U ↪ P) := Fintype.ofFinite _
  have hInitial : (Initial.picture B β).Respects Q := by
    intro R z hz
    obtain ⟨i, x, hx, rfl⟩ := hz
    exact hQ i R x hx
  obtain ⟨W, hW, C, hCQ, hC⟩ := nonInducedConstruction_preserving A
    (Initial.picture B β) Finset.univ.toList κ Q hInitial
  refine ⟨W, hW, C, hCQ, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hC χ
  let θ : (U ↪ P) → κ := fun α =>
    if h : Nonempty (ProjectedEmbedding A (Initial.picture B β) α) then
      χ (f.toEmbedding.comp (Classical.choice h).val)
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ (α : U ↪ P) (e : ProjectedEmbedding A (Initial.picture B β) α) :
      θ α = χ (f.toEmbedding.comp e.val) := by
    have h : Nonempty (ProjectedEmbedding A (Initial.picture B β) α) := ⟨e⟩
    simp only [θ, dite_eq_left h]
    exact hf α (by simp) _ e
  obtain ⟨i, hi⟩ := hRamsey θ
  refine ⟨f.toEmbedding.comp (Initial.copyEmbedding B β i), ?_⟩
  intro e₁ e₂
  have h := hi e₁ e₂
  rw [hθ _ (initialProjectedCopy A B β i e₁),
    hθ _ (initialProjectedCopy A B β i e₂)] at h
  exact h

end StructuralRamsey.Partite

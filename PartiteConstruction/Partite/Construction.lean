import PartiteConstruction.Partite.Picture
import PartiteConstruction.Partite.Fusion

/-! # Finite iteration of the non-induced partite construction

Unlike `backwardFusion`, the existence theorem here discharges every local
Picture Lemma hypothesis. A single finite witness works for every colouring
and simultaneously homogenizes any prescribed finite list of projections.
-/
namespace StructuralRamsey.Partite

universe u v w
variable {L : RelLanguage.{u}} {P : Type v} {U V : Type w}
variable (A : RelStructure L U) (B : System L P V)

def CanonicalOn {W : Type*} (C : System L P W) (profiles : List (U ↪ P))
    (κ : Type*) : Prop :=
  ∀ χ : RelStructure.Embedding A C.toRelStructure → κ,
    ∃ f : Embedding B C, ∀ α ∈ profiles,
      ∀ e₁ e₂ : ProjectedEmbedding A B α,
        χ (f.toEmbedding.comp e₁.val) = χ (f.toEmbedding.comp e₂.val)

/-- The complete finite iteration, starting from an arbitrary finite picture. -/
theorem nonInducedConstruction [Finite U] [Finite V]
    (profiles : List (U ↪ P)) (κ : Type*) [Fintype κ] :
    ∃ (W : Type w) (_ : Finite W) (C : System L P W), CanonicalOn A B C profiles κ := by
  induction profiles with
  | nil =>
      refine ⟨V, inferInstance, B, ?_⟩
      intro χ
      exact ⟨Embedding.id B, fun α h => (List.not_mem_nil h).elim⟩
  | cons α profiles ih =>
      obtain ⟨W, hW, C, hC⟩ := ih
      obtain ⟨X, hX, D, hD⟩ := pictureLemma A C α κ
      refine ⟨X, hX, D, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hD (fun e => χ e.val)
      obtain ⟨f, hf⟩ := hC (fun e => χ (g.toEmbedding.comp e))
      refine ⟨g.comp f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg (e₁.comp f) (e₂.comp f)
      · exact hf β hβ e₁ e₂

/-- In particular, all injective projections can be homogenized together. -/
theorem allProjections [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] :
    ∃ (W : Type w) (_ : Finite W) (C : System L P W),
      ∀ χ : RelStructure.Embedding A C.toRelStructure → κ,
        ∃ f : Embedding B C, ∀ α : U ↪ P,
          ∀ e₁ e₂ : ProjectedEmbedding A B α,
            χ (f.toEmbedding.comp e₁.val) = χ (f.toEmbedding.comp e₂.val) := by
  classical
  let : Fintype (U ↪ P) := Fintype.ofFinite _
  obtain ⟨W, hW, C, hC⟩ := nonInducedConstruction A B (Finset.univ.toList) κ
  refine ⟨W, hW, C, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hC χ
  exact ⟨f, fun α => hf α (by simp)⟩

end StructuralRamsey.Partite

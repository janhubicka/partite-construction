import PartiteConstruction.Partite.Construction

/-! # Preservation of constraints on projected relation tuples

The non-induced construction introduces only relation tuples inherited from
earlier pictures. Every constraint depending on a tuple's partition labels
therefore survives the construction. Strict increase of the distinguished
order relation is one instance; no order-specific API is needed here.
-/
namespace StructuralRamsey.Partite

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {U : Type w} {V : Type z}

def System.Respects (B : System L P V)
    (Q : (R : L.Symbol) → (Fin (L.arity R) → P) → Prop) : Prop :=
  ∀ R x, B.rel R x → Q R (B.part ∘ x)

namespace Picture

theorem respects (A : RelStructure L U) (B : System L P V) (α : U ↪ P) (N : ℕ)
    (Q : (R : L.Symbol) → (Fin (L.arity R) → P) → Prop) (hB : B.Respects Q) :
    (build B α (NonInduced.power A (B.restrict α) N)).Respects Q := by
  intro R z hz
  rcases hz with ⟨y, hy, rfl⟩ | ⟨i, y, hy, rfl⟩
  · obtain ⟨W, x, hx, rfl⟩ := hy
    have heq :
        (build B α (NonInduced.power A (B.restrict α) N)).part ∘
          (Sum.inl ∘ (NonInduced.lineMap W ∘ x)) = B.part ∘ (Subtype.val ∘ x) := by
      funext k
      exact B.restrictedPart_spec α (x k)
    rw [heq]
    exact hB R _ hx
  · have heq :
        (build B α (NonInduced.power A (B.restrict α) N)).part ∘
          (copyEmbedding B α (NonInduced.power A (B.restrict α) N) i ∘ y) = B.part ∘ y := by
      funext k
      exact (copyEmbedding B α (NonInduced.power A (B.restrict α) N) i).map_part (y k)
    change Q R ((build B α (NonInduced.power A (B.restrict α) N)).part ∘
      (copyEmbedding B α (NonInduced.power A (B.restrict α) N) i ∘ y))
    rw [heq]
    exact hB R y hy

end Picture

theorem pictureLemma_preserving (A : RelStructure L U) (B : System L P V) (α : U ↪ P)
    [Finite U] [Finite V] (κ : Type*) [Fintype κ]
    (Q : (R : L.Symbol) → (Fin (L.arity R) → P) → Prop) (hB : B.Respects Q) :
    ∃ (W : Type (max w z)) (_ : Finite W) (C : System L P W),
      C.Respects Q ∧ PictureProperty A B α C κ := by
  classical
  obtain ⟨N, _, hN⟩ := NonInduced.partiteLemma (A := A) (B := B.restrict α) κ
  let D := NonInduced.power A (B.restrict α) N
  exact ⟨Picture.Vertex B α D, inferInstance, Picture.build B α D,
    Picture.respects A B α N Q hB, Picture.property B α D κ hN⟩

variable {V : Type w}

theorem nonInducedConstruction_preserving (A : RelStructure L U) (B : System L P V)
    [Finite U] [Finite V] (profiles : List (U ↪ P)) (κ : Type*) [Fintype κ]
    (Q : (R : L.Symbol) → (Fin (L.arity R) → P) → Prop) (hB : B.Respects Q) :
    ∃ (W : Type w) (_ : Finite W) (C : System L P W),
      C.Respects Q ∧ CanonicalOn A B C profiles κ := by
  induction profiles with
  | nil =>
      refine ⟨V, inferInstance, B, hB, ?_⟩
      intro χ
      exact ⟨Embedding.id B, fun α h => (List.not_mem_nil h).elim⟩
  | cons α profiles ih =>
      obtain ⟨W, hW, C, hCQ, hC⟩ := ih
      obtain ⟨X, hX, D, hDQ, hD⟩ := pictureLemma_preserving A C α κ Q hCQ
      refine ⟨X, hX, D, hDQ, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hD (fun e => χ e.val)
      obtain ⟨f, hf⟩ := hC (fun e => χ (g.toEmbedding.comp e))
      refine ⟨g.comp f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg (e₁.comp f) (e₂.comp f)
      · exact hf β hβ e₁ e₂

end StructuralRamsey.Partite

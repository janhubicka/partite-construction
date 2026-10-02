import PartiteConstruction.Structure.Relationalize

/-! # U-closed graph embeddings and full function embeddings

For graph encodings of set-valued functions, a relational embedding represents
a full embedding exactly when its image is closed under function-value
relations.  This is the bridge from the survey's recursive/U-transversal
relational construction back to structures with functions.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}
variable {A : Structure L V} {B : Structure L W}

/-- Closedness of a relational graph embedding for the function-value
relations. -/
def UClosed (e : RelStructure.Embedding A.graph B.graph) : Prop :=
  ∀ F (x : Fin (L.funcArity F) → V) (y : W),
    B.graph.rel (.inr F) (funcTuple (e ∘ x) y) →
    ∃ z : V, A.graph.rel (.inr F) (funcTuple x z) ∧ e z = y

theorem uClosed_iff_closedMap
    (e : RelStructure.Embedding A.graph B.graph) :
    UClosed e ↔ A.ClosedMap B e := by
  constructor
  · intro h F x y hy
    have hgraph :
        B.graph.rel (.inr F) (funcTuple (e ∘ x) y) := by
      simpa using hy
    obtain ⟨z, hz, heq⟩ := h F x y hgraph
    refine ⟨z, ?_, heq⟩
    simpa using hz
  · intro h F x y hy
    have hy' : y ∈ B.func F (e ∘ x) := by
      simpa using hy
    obtain ⟨z, hz, heq⟩ := h F x y hy'
    refine ⟨z, ?_, heq⟩
    simpa using hz

/-- A full embedding has a U-closed relational graph embedding. -/
theorem Embedding.graph_uClosed (e : Embedding A B) :
    UClosed e.graph := by
  rw [uClosed_iff_closedMap]
  exact e.isHomomorphism.closedMap

/-- Relational graph embedding together with U-closedness reconstructs the
full embedding. -/
def Embedding.ofGraphUClosed
    (e : RelStructure.Embedding A.graph B.graph) (h : UClosed e) :
    Embedding A B :=
  Embedding.ofGraphClosed e ((uClosed_iff_closedMap e).mp h)

/-- Full embeddings and U-closed graph embeddings have the same underlying
maps. -/
def embeddingEquivUClosed :
    Embedding A B ≃ {e : RelStructure.Embedding A.graph B.graph // UClosed e} where
  toFun e := ⟨e.graph, e.graph_uClosed⟩
  invFun e := Embedding.ofGraphUClosed e.1 e.2
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro x
    rfl

/-- U-closed structural Ramsey arrow on relational graph embeddings. -/
def ArrowU (A : Structure L V) (B : Structure L W)
    {X : Type v} (C : Structure L X) (κ : Type*) : Prop :=
  ∀ χ : {e : RelStructure.Embedding A.graph C.graph // UClosed e} → κ,
    ∃ f : {e : RelStructure.Embedding B.graph C.graph // UClosed e},
      ∀ e₁ e₂ : {e : RelStructure.Embedding A.graph B.graph // UClosed e},
        χ ⟨f.1.comp e₁.1, by
          rw [uClosed_iff_closedMap]
          exact (Embedding.ofGraphUClosed f.1 f.2).isHomomorphism.closedMap.comp
            (Embedding.ofGraphUClosed e₁.1 e₁.2).isHomomorphism.closedMap⟩ =
        χ ⟨f.1.comp e₂.1, by
          rw [uClosed_iff_closedMap]
          exact (Embedding.ofGraphUClosed f.1 f.2).isHomomorphism.closedMap.comp
            (Embedding.ofGraphUClosed e₂.1 e₂.2).isHomomorphism.closedMap⟩

end StructuralRamsey.Structure

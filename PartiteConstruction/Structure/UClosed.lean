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


/-- U-closed graph embeddings compose. -/
theorem UClosed.comp
    {X : Type v} {C : Structure L X}
    {e : RelStructure.Embedding A.graph B.graph}
    {g : RelStructure.Embedding B.graph C.graph}
    (hg : UClosed g) (he : UClosed e) :
    UClosed (g.comp e) := by
  rw [uClosed_iff_closedMap]
  exact ((uClosed_iff_closedMap g).mp hg).comp
    ((uClosed_iff_closedMap e).mp he)

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

end StructuralRamsey.Structure

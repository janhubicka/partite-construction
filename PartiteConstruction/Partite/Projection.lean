import PartiteConstruction.Partite.Basic

/-! # Embeddings with a prescribed projection

The survey writes these as Emb(A,B)_α. The source is an L-structure, not an
L_P-structure. Keeping that distinction explicit prevents accidental language
mismatches in the Picture Lemma and its iteration.
-/
namespace StructuralRamsey.Partite

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {U : Type z}

def ProjectedEmbedding (A : RelStructure L V) (B : System L P U) (α : V → P) :=
  {e : RelStructure.Embedding A B.toRelStructure // ∀ x, B.part (e x) = α x}

namespace ProjectedEmbedding

variable {A : RelStructure L V} {B : System L P U} {α : V → P}

def comp {X : Type*} {C : System L P X}
    (f : Embedding B C) (e : ProjectedEmbedding A B α) : ProjectedEmbedding A C α :=
  ⟨f.toEmbedding.comp e.val, fun x => (f.map_part (e.val x)).trans (e.property x)⟩

end ProjectedEmbedding

/-- Put each source vertex in its designated part. Injectivity makes every
relation tuple transversal, including tuples with repeated vertices. -/
def withProjection (A : RelStructure L V) (α : V ↪ P) : System L P V where
  toRelStructure := A
  part := α
  transversal := fun _ _ _ _ _ h => α.injective h

/-- The bijection stated immediately before the Picture Lemma. -/
def projectedEquiv (A : RelStructure L V) (B : System L P U) (α : V ↪ P) :
    ProjectedEmbedding A B α ≃ Embedding (withProjection A α) B where
  toFun e := { toEmbedding := e.val, map_part := e.property }
  invFun e := ⟨e.toEmbedding, e.map_part⟩
  left_inv _ := rfl
  right_inv _ := rfl

end StructuralRamsey.Partite

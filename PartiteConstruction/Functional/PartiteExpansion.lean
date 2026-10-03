import PartiteConstruction.Functional.ClosedPartite
import PartiteConstruction.Partite.Predicates

/-! # Part predicates inside the graph language

The recursive construction temporarily treats a D-partite system as an
ordinary structure by naming its outer parts with unary relations.  This file
packages that representation at the original relation/function-language level,
so the existing U-closed machinery can be reused without changing the function
symbols.

For a language L and a part set P, L.withParts P adds one unary relation symbol
for every p : P and leaves the function symbols unchanged.  The graph of a
P-partite system then expands to an (L.withParts P).graph-structure.  Ordinary
embeddings of these expanded graphs are exactly part-preserving embeddings,
and closed embeddings are exactly closed partite embeddings.
-/
namespace StructuralRamsey

universe u v

namespace Language

/-- Add one unary relation symbol for every named part, leaving functions
unchanged. -/
def withParts (L : Language.{u}) (P : Type v) : Language.{max u v} where
  RelSymbol := ULift.{v, u} L.RelSymbol ⊕ ULift.{u, v} P
  FuncSymbol := ULift.{v, u} L.FuncSymbol
  relArity
    | .inl R => L.relArity R.down
    | .inr _ => 1
  funcArity F := L.funcArity F.down

theorem withParts_positiveFuncArity
    {L : Language.{u}} {P : Type v}
    (h : L.PositiveFuncArity) :
    (L.withParts P).PositiveFuncArity := by
  intro F
  exact h F.down

end Language

namespace Partite.PartExpansion

open RelStructure Structure

variable {L : Language.{u}} {P V : Type v}

/-- Expand a graph-partite system by unary relations naming its parts. -/
def expandGraph (B : Partite.System L.graph P V) :
    RelStructure (L.withParts P).graph V where
  rel
    | .inl (.inl R), x => B.rel (.inl R.down) x
    | .inl (.inr p), x => B.part (x (0 : Fin 1)) = p.down
    | .inr F, x => B.rel (.inr F.down) x

@[simp] theorem expandGraph_rel
    (B : Partite.System L.graph P V)
    (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    (expandGraph B).rel (.inl (.inl (ULift.up R))) x ↔
      B.rel (.inl R) x :=
  Iff.rfl

@[simp] theorem expandGraph_func
    (B : Partite.System L.graph P V)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F + 1) → V) :
    (expandGraph B).rel (.inr (ULift.up F)) x ↔
      B.rel (.inr F) x :=
  Iff.rfl

@[simp] theorem expandGraph_part
    (B : Partite.System L.graph P V)
    (p : P) (x : Fin 1 → V) :
    (expandGraph B).rel (.inl (.inr (ULift.up p))) x ↔
      B.part (x 0) = p :=
  Iff.rfl

namespace Embedding

variable {W : Type v}
variable {A : Partite.System L.graph P V}
variable {B : Partite.System L.graph P W}

/-- A part-preserving embedding expands to an embedding after naming parts by
unary relations. -/
def expandGraph (e : Partite.Embedding A B) :
    RelStructure.Embedding
      (PartExpansion.expandGraph A)
      (PartExpansion.expandGraph B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        cases R with
        | inl R =>
            exact e.map_rel_iff (.inl R.down) x
        | inr p =>
            change
              B.part (e (x (0 : Fin 1))) = p.down ↔
                A.part (x (0 : Fin 1)) = p.down
            rw [e.map_part]
    | inr F =>
        exact e.map_rel_iff (.inr F.down) x

/-- An embedding after naming the parts automatically preserves the original
part map. -/
def ofExpandedGraph
    (e : RelStructure.Embedding
      (PartExpansion.expandGraph A)
      (PartExpansion.expandGraph B)) :
    Partite.Embedding A B where
  toEmbedding := {
    toFun := e
    injective := e.injective
    map_rel_iff := by
      intro R x
      cases R with
      | inl R =>
          exact e.map_rel_iff (.inl (.inl (ULift.up R))) x
      | inr F =>
          exact e.map_rel_iff (.inr (ULift.up F)) x
  }
  map_part := by
    intro x
    have h :=
      (e.map_rel_iff
        (.inl (.inr (ULift.up (A.part x))))
        (fun _ : Fin 1 => x)).mpr rfl
    exact h

/-- Partite embeddings are equivalent to embeddings of the expanded graphs. -/
def expandedGraphEquiv :
    Partite.Embedding A B ≃
      RelStructure.Embedding
        (PartExpansion.expandGraph A)
        (PartExpansion.expandGraph B) where
  toFun := expandGraph
  invFun := ofExpandedGraph
  left_inv := by
    intro e
    apply Partite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.Embedding.ext
    intro x
    rfl

end Embedding

namespace ClosedEmbedding

variable {W : Type v}
variable {A : Partite.System L.graph P V}
variable {B : Partite.System L.graph P W}

/-- A closed partite embedding remains closed after naming the parts. -/
def expandGraph (e : Partite.Closed.Embedding A B) :
    RelStructure.ClosedEmbedding
      (PartExpansion.expandGraph A)
      (PartExpansion.expandGraph B) where
  toEmbedding := PartExpansion.Embedding.expandGraph e.1
  closed := by
    intro F x y hy
    exact e.2 F.down x y hy

/-- Closedness in the expanded graph language is exactly the original
function-closedness, so an expanded closed embedding decodes to a closed
partite embedding. -/
def ofExpandedGraph
    (e : RelStructure.ClosedEmbedding
      (PartExpansion.expandGraph A)
      (PartExpansion.expandGraph B)) :
    Partite.Closed.Embedding A B := by
  let pe : Partite.Embedding A B :=
    PartExpansion.Embedding.ofExpandedGraph e.toEmbedding
  refine ⟨pe, ?_⟩
  intro F x y hy
  exact e.closed (ULift.up F) x y hy

/-- Closed partite embeddings are equivalent to closed embeddings after naming
parts by unary relations. -/
def expandedGraphEquiv :
    Partite.Closed.Embedding A B ≃
      RelStructure.ClosedEmbedding
        (PartExpansion.expandGraph A)
        (PartExpansion.expandGraph B) where
  toFun := expandGraph
  invFun := ofExpandedGraph
  left_inv := by
    intro e
    apply Partite.Closed.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl

end ClosedEmbedding

end Partite.PartExpansion
end StructuralRamsey

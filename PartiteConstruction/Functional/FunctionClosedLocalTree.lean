import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Structure.WeakSubstructure

/-! # Local completion by function-closed graph trees

The domain-aware recursive partite construction naturally lives in the graph
encoding.  To recover a genuine function-language local tree theorem, both
pieces of closure data have to be retained:

* every gluing root in the relational tree is function-closed; and
* the local map from the tested closed substructure into that tree is itself
  function-closed.

This file packages that intermediate invariant and the decoding theorem back
to full relation/function structures.
-/

namespace StructuralRamsey

open Structure

universe u v

namespace RelStructure

variable {L : Language.{u}}
variable {V W : Type v}

/-- A relational graph structure admits a closed embedding into a
function-closed tree amalgam of copies of the base graph. -/
def FunctionClosedHasTreeCompletion
    (Base : RelStructure L.graph V)
    (C : RelStructure L.graph W) : Prop :=
  ∃ (Y : Type v) (T : RelStructure L.graph Y),
    FunctionClosedTreeAmalgam Base Y T ∧
    Nonempty (ClosedEmbedding C T)

/-- Every function-closed finite test on at most n vertices admits a closed
embedding into a function-closed tree amalgam of copies of Base. -/
def FunctionClosedLocallyTreeCompletable
    (Base : RelStructure L.graph V)
    (C : RelStructure L.graph W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    FunctionClosedSet C (↑S : Set W) →
    FunctionClosedHasTreeCompletion Base (C.induce (↑S : Set W))

/-- Full closedness of a subset in the function language is exactly enough
for the same carrier to be function-closed in the graph encoding. -/
theorem functionClosedSet_graph_of_isClosed
    (A : Structure L W) (S : Set W)
    (hS : A.IsClosed S) :
    FunctionClosedSet A.graph S := by
  intro F x y hy hx
  have hyA : y ∈ A.func F x :=
    (Structure.graph_func_snoc A F x y).mp hy
  exact hS F x hx hyA

/-- For a genuine closed substructure, graph-then-induce and
induce-then-graph are related by the identity closed embedding. -/
def closedInduceGraph
    (A : Structure L W) (S : Set W)
    (hS : A.IsClosed S) :
    ClosedEmbedding (A.induce S hS).graph (A.graph.induce S) where
  toEmbedding := {
    toFun := id
    injective := Function.injective_id
    map_rel_iff := by
      intro R x
      cases R <;> rfl
  }
  closed := by
    intro F x y hy
    refine ⟨y, ?_, rfl⟩
    change
      (A.induce S hS).graph.rel (.inr F)
        (Structure.funcTuple x y)
    change
      (A.graph.induce S).rel (.inr F)
        (Structure.funcTuple x y) at hy
    exact hy

namespace FunctionClosedLocallyTreeCompletable

variable {Base : Structure L V}
variable {C : Structure L W}
variable {n : ℕ}

/-- Decode the graph-level closure-aware local invariant to the user-facing
full function-language local tree theorem. -/
theorem toFunctional
    (hBase : Base.Irreducible)
    (h :
      FunctionClosedLocallyTreeCompletable
        Base.graph C.graph n) :
    Structure.LocallyClosedTreeCompletable Base C n := by
  intro S hcard hS
  have hSgraph :
      FunctionClosedSet C.graph (↑S : Set W) :=
    functionClosedSet_graph_of_isClosed C (↑S : Set W) hS
  obtain ⟨Y, T, hTree, he⟩ :=
    h S hcard hSgraph
  let src :
      ClosedEmbedding
        (C.induce (↑S : Set W) hS).graph
        (C.graph.induce (↑S : Set W)) :=
    closedInduceGraph C (↑S : Set W) hS
  let e : ClosedEmbedding
      (C.induce (↑S : Set W) hS).graph T :=
    ClosedEmbedding.comp he.some src
  let f : Structure.Embedding
      (C.induce (↑S : Set W) hS)
      (Structure.ofGraph T) :=
    Structure.Embedding.ofClosedGraphTarget e
  have hTreeFull :
      Structure.TreeAmalgam Base Y (Structure.ofGraph T) :=
    RelStructure.FunctionClosedTreeAmalgam.toFunctional
      hBase hTree
  exact ⟨Y, Structure.ofGraph T, hTreeFull, f,
    f.isHomomorphismEmbedding⟩

end FunctionClosedLocallyTreeCompletable

end RelStructure
end StructuralRamsey

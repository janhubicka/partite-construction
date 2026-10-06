import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Functional.FunctionDomains
import PartiteConstruction.Functional.ClosedLiftEmbedding
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
variable {U V W : Type v}

/-- A relational graph structure admits a closed embedding into a
function-closed tree amalgam of copies of the base graph. -/
def FunctionClosedHasTreeCompletion
    (Base : RelStructure L.graph V)
    (C : RelStructure L.graph W) : Prop :=
  ∃ (Y : Type v) (T : RelStructure L.graph Y),
    FunctionClosedTreeAmalgam Base Y T ∧
    Nonempty (ClosedEmbedding C T)

namespace FunctionClosedHasTreeCompletion

/-- Glue two explicit closure-aware strict-tree witnesses across a source free
amalgam.  The source root embeddings must be function-closed, and their images
in the two target trees must satisfy the survey's irreducible-containment
condition.  No further closure argument is needed: compatible closed side
embeddings lift to a closed whole embedding. -/
theorem glue
    {H E F X YL YR : Type v}
    {Root : RelStructure L.graph H}
    {Left : RelStructure L.graph E}
    {Right : RelStructure L.graph F}
    {Whole : RelStructure L.graph X}
    {Base : RelStructure L.graph V}
    {TL : RelStructure L.graph YL}
    {TR : RelStructure L.graph YR}
    {sL : Embedding Root Left}
    {sR : Embedding Root Right}
    {iL : Embedding Left Whole}
    {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hsL : FunctionClosedMap Root Left sL)
    (hsR : FunctionClosedMap Root Right sR)
    (hTreeL : FunctionClosedTreeAmalgam Base YL TL)
    (hTreeR : FunctionClosedTreeAmalgam Base YR TR)
    (eL : ClosedEmbedding Left TL)
    (eR : ClosedEmbedding Right TR)
    (hcL : (eL.toEmbedding.comp sL).ContainedInIrreducible)
    (hcR : (eR.toEmbedding.comp sR).ContainedInIrreducible) :
    FunctionClosedHasTreeCompletion Base Whole := by
  classical
  let tL : Embedding Root TL := eL.toEmbedding.comp sL
  let tR : Embedding Root TR := eR.toEmbedding.comp sR
  let Target := FreeAmalgam.amalgam Root TL TR tL tR
  let jL := FreeAmalgam.leftEmbedding Root TL TR tL tR
  let jR := FreeAmalgam.rightEmbedding Root TL TR tL tR
  have hTgt : IsFreeAmalgam tL tR jL jR :=
    FreeAmalgam.isFreeAmalgam Root TL TR tL tR
  have htLclosed : FunctionClosedMap Root TL tL :=
    eL.closed.comp hsL
  have htRclosed : FunctionClosedMap Root TR tR :=
    eR.closed.comp hsR
  have hTree :
      FunctionClosedTreeAmalgam Base
        (FreeAmalgam.Vertex Root TL TR tL tR) Target :=
    FunctionClosedTreeAmalgam.glue
      hTreeL hTreeR tL tR htLclosed htRclosed
      hcL hcR jL jR hTgt
  have hcompatL : ∀ d, eL (sL d) = tL d := fun _ => rfl
  have hcompatR : ∀ d, eR (sR d) = tR d := fun _ => rfl
  have hexL :
      IsFreeAmalgam.ReflectsOverlap id sL tL eL.toEmbedding := by
    intro a g hag
    refine ⟨g, ?_, rfl⟩
    apply eL.toEmbedding.injective
    exact hag
  have hexR :
      IsFreeAmalgam.ReflectsOverlap id sR tR eR.toEmbedding := by
    intro b g hbg
    refine ⟨g, ?_, rfl⟩
    apply eR.toEmbedding.injective
    exact hbg
  let e : ClosedEmbedding Whole Target :=
    hSrc.liftClosedEmbedding hTgt id eL eR
      hcompatL hcompatR hexL hexR
  exact ⟨_, Target, hTree, ⟨e⟩⟩

/-- A closed embedding into one copy of the base is already a
function-closed tree completion. -/
theorem of_closedEmbedding
    {Base : RelStructure L.graph V}
    {C : RelStructure L.graph W}
    (e : ClosedEmbedding C Base) :
    FunctionClosedHasTreeCompletion Base C := by
  have hTree :
      FunctionClosedTreeAmalgam Base V Base :=
    FunctionClosedTreeAmalgam.copy (RelStructure.Iso.refl Base)
  exact ⟨V, Base, hTree, ⟨e⟩⟩

/-- In the domain-expanded partial-function language, the standard
semi-closed criterion upgrades an ordinary embedding into one Base copy to
the closed embedding required by the local tree invariant. -/
theorem of_localSemiClosed
    {A : RelStructure L.withFunctionDomains.graph U}
    {Base : RelStructure L.withFunctionDomains.graph V}
    (hBaseRoot : Base.OutputImpliesDomain)
    (e : RelStructure.Embedding A Base)
    (hLocal : LocallySingleValuedOn A Base e)
    (hAtotal : A.FunctionDomainTotal) :
    FunctionClosedHasTreeCompletion Base A :=
  of_closedEmbedding
    (closedEmbedding_of_localSemiClosed
      hBaseRoot e hLocal hAtotal)

end FunctionClosedHasTreeCompletion

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

variable {BaseGraph : RelStructure L.graph V}
variable {CGraph : RelStructure L.graph W}
variable {m : ℕ}

/-- Monotonicity in the local size bound. -/
theorem mono
    (h : FunctionClosedLocallyTreeCompletable BaseGraph CGraph n)
    (hmn : m ≤ n) :
    FunctionClosedLocallyTreeCompletable BaseGraph CGraph m := by
  intro S hcard hS
  exact h S (hcard.trans hmn) hS

/-- A function-closed tree amalgam is locally complete at every finite scale,
using the closed inclusion of the tested set. -/
theorem of_treeAmalgam
    (hTree : FunctionClosedTreeAmalgam BaseGraph W CGraph)
    (n : ℕ) :
    FunctionClosedLocallyTreeCompletable BaseGraph CGraph n := by
  intro S _ hS
  let e : ClosedEmbedding
      (CGraph.induce (↑S : Set W)) CGraph :=
    ClosedEmbedding.inclusion CGraph (↑S : Set W) hS
  exact ⟨W, CGraph, hTree, ⟨e⟩⟩

/-- One copy of the base graph is locally complete at every scale. -/
theorem base
    (BaseGraph : RelStructure L.graph V) (n : ℕ) :
    FunctionClosedLocallyTreeCompletable BaseGraph BaseGraph n := by
  have hTree :
      FunctionClosedTreeAmalgam BaseGraph V BaseGraph :=
    FunctionClosedTreeAmalgam.copy (RelStructure.Iso.refl BaseGraph)
  exact of_treeAmalgam hTree n

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

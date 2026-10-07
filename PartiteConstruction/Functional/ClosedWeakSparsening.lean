import PartiteConstruction.Functional.ClosedConstructionWeakTree
import PartiteConstruction.Functional.InducedConstruction

/-! # Functional Ramsey with one-level weak graph-tree control

The **same** U-closed induced construction gives both the ordinary full
function-language Ramsey arrow and one additional vertex of weak graph-tree
local completability.  This is stronger than applying the ordinary relational
induced theorem to the graph language: that construction need not preserve
full function embeddings or the desired functional Ramsey arrow.

This theorem intentionally distinguishes its conclusions:
* The Ramsey arrow uses full embeddings of set-valued-function structures.
* The local-tree witness for arbitrary weak tests lives in the *relational*
  graph language.  No fibre-surjectivity or function-closed gluing is asserted.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {U V P : Type v}

/-- One complete U-closed induced partite construction adds one vertex to
the weak graph-tree local bound while preserving the full functional Ramsey
arrow.  This proof uses only the actual closed functional Picture steps. -/
theorem inducedRamsey_weakTreeGraph_succ
    (A : Structure L U)
    (B : Structure L V)
    (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.Irreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ)
    (hD : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A.graph) (D := D.graph) (C := D.graph)
      (B := B.graph) id n) :
    ∃ T : Partite.Closed.Construction.Stage B.graph D.graph,
      Structure.Arrow A B
        (Structure.ofGraph T.system.toRelStructure) κ ∧
      WeakLocallyTreeCompletable B
        (Structure.ofGraph T.system.toRelStructure) (n + 1) := by
  have hClosed :
      RelStructure.ClosedArrow A.graph B.graph D.graph κ :=
    (Structure.arrow_iff_closedGraph
      (A := A) (B := B) D κ).mp hRamsey
  have hD' : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A.graph) (D := D.graph) (C := D.graph)
      (B := B.graph) id ((n + 1) - 1) := by
    simpa using hD
  obtain ⟨T, hArrow, hLocal⟩ :=
    Partite.Closed.Construction.inducedConstruction_withWeakTree
      A.graph B.graph D.graph hpos κ hClosed
      hA eAB.graph (n + 1) (by omega) hD'
  refine ⟨T, ?_, ?_⟩
  · exact
      (Structure.arrow_ofGraph_iff_closed
        (A := A) (B := B) T.system.toRelStructure κ).mpr hArrow
  · exact WeakLocallyTreeCompletable.ofGraph
      B T.system.toRelStructure (n + 1) hLocal

end StructuralRamsey.Structure

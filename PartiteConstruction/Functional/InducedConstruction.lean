import PartiteConstruction.Functional.ClosedConstruction

/-! # Functional induced Ramsey theorem

This is the full relation/function consequence of the corrected U-closed graph
construction.  It deliberately does not claim that the graph-stage partition
projection is a homomorphism in the original set-valued-function language;
that stronger invariant is not preserved by the free Picture construction.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Induced Ramsey construction for finite structures with relations and
positive-arity set-valued functions.  The witness is reconstructed from the
U-transversal graph-partite stage produced by the closed construction. -/
theorem inducedRamsey
    (A : Structure L U)
    (B : Structure L V)
    (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ) :
    ∃ T : Partite.Closed.Construction.Stage B.graph D.graph,
      Structure.Arrow A B
        (Structure.ofGraph T.system.toRelStructure) κ := by
  have hClosed :
      RelStructure.ClosedArrow A.graph B.graph D.graph κ :=
    (Structure.arrow_iff_closedGraph
      (A := A) (B := B) D κ).mp hRamsey
  obtain ⟨T, hT⟩ :=
    Partite.Closed.Construction.inducedConstruction
      A.graph B.graph D.graph hpos κ hClosed
  refine ⟨T, ?_⟩
  exact
    (Structure.arrow_ofGraph_iff_closed
      (A := A) (B := B) T.system.toRelStructure κ).mpr hT

end StructuralRamsey.Structure

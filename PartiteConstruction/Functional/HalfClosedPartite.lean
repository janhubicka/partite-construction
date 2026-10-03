import PartiteConstruction.Functional.PartPredicates

/-! # Native half-closed partite construction through L_P

This packages the manuscript's instruction to view a partite system as an
L_P-structure, apply the half-closed construction there, and reinterpret the
result back at the original part level.

The nested output is flattened through the intermediate target.  Its
U-transversality follows directly by composition of the inner and outer
U-transversality invariants; no tuple-deletion or closed-copy-coverage
assumption is needed for this step.
-/
namespace StructuralRamsey.Partite.HalfClosed

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- Corrected positive-arity half-closed partite construction in native
partite language. -/
theorem inducedPartite
    (A : Partite.System L.graph P U)
    (B : Partite.System L.graph P V)
    (D : Partite.System L.graph P W)
    [Finite U] [Finite V] [Finite W]
    (hpos : L.PositiveFuncArity)
    (hD : D.FunctionOutputTransversal)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Partite.HalfClosedArrow
      (A := A) (B := B) (D := D) κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.FunctionOutputTransversal ∧
      Partite.Closed.Arrow A B C κ := by
  classical
  have hRamseyExp :
      RelStructure.HalfClosedArrow
        A.expandFunctional B.expandFunctional D.expandFunctional κ :=
    (Partite.halfClosedArrow_iff_functionalExpanded
      (A := A) (B := B) (D := D) (κ := κ)).mp hRamsey
  letI : Nonempty
      (RelStructure.Embedding B.expandFunctional D.expandFunctional) :=
    RelStructure.nonempty_embedding_of_halfClosedArrow
      A.expandFunctional B.expandFunctional D.expandFunctional κ
      hRamseyExp
  obtain ⟨T, hArrowExp⟩ :=
    Partite.HalfClosed.Construction.inducedConstruction
      A.expandFunctional B.expandFunctional D.expandFunctional
      hpos.withParts κ hRamseyExp
  let C0 : Partite.System L.graph W T.Vertex :=
    Partite.System.ofFunctionalExpansion
      (L := L) (P := P) T.system
  have hC0 : C0.IsPartiteOver D.toRelStructure :=
    Partite.isPartiteOver_of_functionalExpanded
      (L := L) (P := P) D T.system T.isPartite
  let C : Partite.System L.graph P T.Vertex :=
    Partite.Nested.flatten D C0 hC0
  have hInner : C0.FunctionOutputTransversal :=
    Partite.functionOutputTransversal_of_expanded
      (L := L) (P := P) T.system T.uTransversal
  have hU : C.FunctionOutputTransversal := by
    exact Partite.Nested.flatten_uTransversal_comp
      D C0 hC0 hD hInner
  have hArrow : Partite.Closed.Arrow A B C κ := by
    exact Partite.closedArrow_flattened_of_functionalExpanded
      (L := L) (P := P)
      A B D T.system T.isPartite κ hArrowExp
  exact ⟨T.Vertex, inferInstance, C, hU, hArrow⟩

end StructuralRamsey.Partite.HalfClosed

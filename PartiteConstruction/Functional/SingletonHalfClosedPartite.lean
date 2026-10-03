import PartiteConstruction.Functional.SingletonHalfClosedConstruction
import PartiteConstruction.Functional.HalfClosedPartite

/-! # Native singleton-valued half-closed partite repair

This is the corrected second stage of the recursive partite construction.
Unlike `inducedPartiteOver`, the intermediate target E is not assumed
U-transversal.  Instead the copied previous stage B is globally
singleton-valued.  The expanded half-closed construction preserves that
stronger invariant; after flattening it yields a singleton-valued, hence
U-transversal, D-partite stage.
-/
namespace StructuralRamsey.Partite.HalfClosed

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- Repair a half-closed local picture in the partial-function case, while
preserving an outer D-partite projection.  No U-transversality hypothesis is
needed on the intermediate picture E. -/
theorem inducedPartiteOver_singleton
    (A : Partite.System L.graph P U)
    (B : Partite.System L.graph P V)
    (E : Partite.System L.graph P W)
    {D₀ : RelStructure L.graph P}
    [Finite U] [Finite V] [Finite W]
    (hpos : L.PositiveFuncArity)
    (hB : B.FunctionOutputSingleValued)
    (hE : E.IsPartiteOver D₀)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Partite.HalfClosedArrow
      (A := A) (B := B) (D := E) κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D₀ ∧
      C.FunctionOutputSingleValued ∧
      Partite.Closed.Arrow A B C κ := by
  classical
  have hRamseyExp :
      RelStructure.HalfClosedArrow
        A.expandFunctional
        B.expandFunctional
        E.expandFunctional κ :=
    (Partite.halfClosedArrow_iff_functionalExpanded
      (A := A) (B := B) (D := E) (κ := κ)).mp hRamsey
  have hBExp :
      B.expandFunctional.FunctionOutputSingleValued :=
    Partite.singleValued_expandFunctional hB
  letI : Nonempty
      (RelStructure.Embedding
        B.expandFunctional E.expandFunctional) :=
    RelStructure.nonempty_embedding_of_halfClosedArrow
      A.expandFunctional B.expandFunctional
      E.expandFunctional κ hRamseyExp
  obtain ⟨T, hArrowExp⟩ :=
    Partite.HalfClosed.Construction.inducedConstruction_singleValued
      A.expandFunctional B.expandFunctional E.expandFunctional
      hpos.withParts hBExp κ hRamseyExp
  let C0 : Partite.System L.graph W T.Vertex :=
    Partite.System.ofFunctionalExpansion
      (L := L) (P := P) T.system
  have hC0 : C0.IsPartiteOver E.toRelStructure :=
    Partite.isPartiteOver_of_functionalExpanded
      (L := L) (P := P) E T.system T.isPartite
  let C : Partite.System L.graph P T.Vertex :=
    Partite.Nested.flatten E C0 hC0
  have hPartite : C.IsPartiteOver D₀ :=
    Partite.Nested.flatten_isPartiteOver E C0 hE hC0
  have hInnerSingle : C0.FunctionOutputSingleValued :=
    Partite.singleValued_ofFunctionalExpansion
      (L := L) (P := P) T.singleValued
  have hSingle : C.FunctionOutputSingleValued :=
    Partite.Nested.flatten_singleValued E C0 hC0 hInnerSingle
  have hArrow : Partite.Closed.Arrow A B C κ :=
    Partite.closedArrow_flattened_of_functionalExpanded
      (L := L) (P := P)
      A B E T.system T.isPartite κ hArrowExp
  exact ⟨T.Vertex, inferInstance, C,
    hPartite, hSingle, hArrow⟩

/-- The singleton repair automatically supplies the U-transversality needed by
the outer recursive stage. -/
theorem inducedPartiteOver_singleton_uTransversal
    (A : Partite.System L.graph P U)
    (B : Partite.System L.graph P V)
    (E : Partite.System L.graph P W)
    {D₀ : RelStructure L.graph P}
    [Finite U] [Finite V] [Finite W]
    (hpos : L.PositiveFuncArity)
    (hB : B.FunctionOutputSingleValued)
    (hE : E.IsPartiteOver D₀)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Partite.HalfClosedArrow
      (A := A) (B := B) (D := E) κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D₀ ∧
      C.FunctionOutputSingleValued ∧
      C.FunctionOutputTransversal ∧
      Partite.Closed.Arrow A B C κ := by
  obtain ⟨X, hX, C, hPartite, hSingle, hArrow⟩ :=
    inducedPartiteOver_singleton
      A B E hpos hB hE κ hRamsey
  exact ⟨X, hX, C, hPartite, hSingle,
    hSingle.uTransversal, hArrow⟩

end StructuralRamsey.Partite.HalfClosed

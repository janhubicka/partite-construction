import PartiteConstruction.Functional.HalfClosedConstruction

/-! # The half-closed theorem with an unpacked witness

This is the direct interface to Appendix A, lemma `lem:rpartite`. Unlike the
native nested-flattening wrappers, the input D need not be U-transversal.
Only the output is repaired to be U-transversal. The initial disjoint union
requires positive function arity; no irreducibility assumption is used.
-/
namespace StructuralRamsey.Partite.HalfClosed

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A half-closed arrow yields a finite U-transversal D-partite witness for
the genuine closed arrow. This hides the construction's stage and initial
nonemptiness bookkeeping from downstream applications. -/
theorem ramseyPartiteWitness
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.HalfClosedArrow A B D κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D ∧ C.FunctionOutputTransversal ∧
      RelStructure.ClosedArrow A B C.toRelStructure κ := by
  classical
  obtain ⟨T, hArrow⟩ :=
    Construction.inducedConstruction A B D hpos κ hRamsey
  exact ⟨T.Vertex, T.finiteVertex, T.system,
    T.isPartite, T.uTransversal, hArrow⟩

end StructuralRamsey.Partite.HalfClosed

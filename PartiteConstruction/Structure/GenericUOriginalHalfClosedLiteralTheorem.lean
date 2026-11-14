import PartiteConstruction.Structure.GenericUOriginalHalfClosedTheorem
import PartiteConstruction.Structure.GenericUHalfClosedLiteralQuantifiers

/-!
# Track F — half-closed partite theorem from precisely the printed hypothesis

The explicit-lift formulation required by the graph construction is
equivalent to the printed condition on the actual ordinary B→D embedding.
This wrapper states the same existential conclusion directly from the
literal composite-closedness-and-monochromaticity premise.
-/

namespace StructuralRamsey.Partite.OriginalUClosed

universe u v
variable {L : RelLanguage.{u}} {P T V : Type v}

/-- Original arbitrary (L,U) half-closed partite construction, directly
assuming the literal survey half-closed condition (without a lift). -/
theorem halfClosedPartiteWitness_of_literal
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    [Finite T] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.OriginalUHalfClosedArrowLiteral A B D U
      (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) κ) :
    ∃ (X : Type v) (_ : Finite X) (C : Partite.System L P X),
      C.IsPartiteOver D ∧
      C.OriginalUOutputTransversal U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) ∧
      RelStructure.OriginalUClosedArrow A B C.toRelStructure U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) κ := by
  apply halfClosedPartiteWitness A B D U hU κ
  exact (RelStructure.originalUHalfClosedArrowLiteral_iff A B D U
    (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) κ).mp hRamsey

end StructuralRamsey.Partite.OriginalUClosed

import PartiteConstruction.Structure.GenericUGraphSemantics
import PartiteConstruction.Functional.Closed

/-!
# Arbitrary (L,U) output transversality equals function-graph transversality

For each distinguished R of arity n+1, the output fibre over an n-tuple
must contain at most one vertex of each named part. The semantic dictionary
established in the preceding Track F branch identifies the literal original
R-tuples with the true set-valued-function graph incidences, on unchanged
vertices and part maps.

This is a predicate equivalence, not merely one implication. Empty and
multi-valued fibres and repeated coordinates are included.
-/

namespace StructuralRamsey.Partite.System

universe u v
variable {L : RelLanguage.{u}} {P V : Type v}

/-- Original arbitrary-relational U-transversality: each actual last-output
fibre of a distinguished relation meets every part in at most one vertex. -/
def OriginalUOutputTransversal
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) : Prop :=
  ∀ (F : U) (x : Fin (L.arity F.1 - 1) → V) (y z : V),
    B.rel F.1 (RelLanguage.appendU L U hU F x y) →
    B.rel F.1 (RelLanguage.appendU L U hU F x z) →
    B.part y = B.part z → y = z

/-- The graph relation at the literal function-tuple is precisely the
original designated last-coordinate relation, with no added coherence
hypothesis or change of tuple values. -/
theorem reducedUGraph_func_snoc_iff
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    (B.asReducedUGraph U hU).rel (.inr F)
      (Structure.funcTuple x y) ↔
    B.rel F.1 (RelLanguage.appendU L U hU F x y) := by
  calc
    (B.asReducedUGraph U hU).rel (.inr F)
        (Structure.funcTuple x y) ↔
      (B.toRelStructure.asUFunctionsReduced U hU).graph.rel (.inr F)
        (Structure.funcTuple x y) :=
      B.asReducedUGraph_iff_functionGraph U hU (.inr F) _
    _ ↔ y ∈ (B.toRelStructure.asUFunctionsReduced U hU).func F x :=
      Structure.graph_func_snoc
        (B.toRelStructure.asUFunctionsReduced U hU) F x y
    _ ↔ B.rel F.1 (RelLanguage.appendU L U hU F x y) := Iff.rfl

/-- Exactly the full survey condition: no strengthened functionality or
totality requirement is introduced in the graph translation. -/
theorem originalUOutputTransversal_iff
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    B.OriginalUOutputTransversal U hU ↔
      (B.asReducedUGraph U hU).FunctionOutputTransversal := by
  constructor
  · intro h F x y z hy hz hp
    exact h F x y z
      ((reducedUGraph_func_snoc_iff B U hU F x y).mp hy)
      ((reducedUGraph_func_snoc_iff B U hU F x z).mp hz) hp
  · intro h F x y z hy hz hp
    exact h F x y z
      ((reducedUGraph_func_snoc_iff B U hU F x y).mpr hy)
      ((reducedUGraph_func_snoc_iff B U hU F x z).mpr hz) hp

end StructuralRamsey.Partite.System

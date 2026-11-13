import PartiteConstruction.Structure.GenericUOutputTransversal
import PartiteConstruction.Structure.GenericUGraphPartiteInverse
import PartiteConstruction.Structure.GenericUGraphInverse
import PartiteConstruction.Functional.Closed

/-!
# Track F — U-output transversality of an arbitrary decoded graph witness

The graph-language Picture and half-closed lemmas produce an ARBITRARY
partite system over the nonredundant set-valued-function graph signature,
not necessarily the graph of a previously encoded original structure.

Decoding such a witness must preserve its exact function-output-fibre
transversality in the original (L,U) language. The proof uses the
graph↔original relation incidence round trip and the unchanged part map.
It does not require a coherence hypothesis or singleton-valued functions.
-/

namespace StructuralRamsey.Partite.System

universe u v
variable {L : RelLanguage.{u}} {P V : Type v}

/-- Re-encoding the original relational decode of ANY graph-language
partite system preserves the exact graph output-fibre transversality. -/
theorem functionOutputTransversal_reencode_iff
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V) :
    ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph
      U hU).FunctionOutputTransversal ↔
      B.FunctionOutputTransversal := by
  constructor
  · intro h F x y z hy hz hp
    have hy' :
        ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph
          U hU).rel (.inr F) (Structure.funcTuple x y) :=
      (RelStructure.as_fromReducedUGraph_rel_iff U hU
        B.toRelStructure (.inr F) (Structure.funcTuple x y)).mpr hy
    have hz' :
        ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph
          U hU).rel (.inr F) (Structure.funcTuple x z) :=
      (RelStructure.as_fromReducedUGraph_rel_iff U hU
        B.toRelStructure (.inr F) (Structure.funcTuple x z)).mpr hz
    exact h F x y z hy' hz' hp
  · intro h F x y z hy hz hp
    have hy' : B.rel (.inr F) (Structure.funcTuple x y) :=
      (RelStructure.as_fromReducedUGraph_rel_iff U hU
        B.toRelStructure (.inr F) (Structure.funcTuple x y)).mp hy
    have hz' : B.rel (.inr F) (Structure.funcTuple x z) :=
      (RelStructure.as_fromReducedUGraph_rel_iff U hU
        B.toRelStructure (.inr F) (Structure.funcTuple x z)).mp hz
    exact h F x y z hy' hz' hp

/-- The exact arbitrary-target equivalence needed to decode original
U-transversal partite witnesses from the graph Picture/half-closed lemmas.
The original and graph carriers and their part maps are identical. -/
theorem originalUOutputTransversal_decode_iff
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V) :
    (Partite.System.fromReducedUGraph U hU B).OriginalUOutputTransversal
      U hU ↔
      B.FunctionOutputTransversal := by
  exact ((Partite.System.fromReducedUGraph U hU B).originalUOutputTransversal_iff
      U hU).trans
      (functionOutputTransversal_reencode_iff U hU B)

end StructuralRamsey.Partite.System

import PartiteConstruction.Structure.GenericUFunctionalOrderedArrowTransfer
import PartiteConstruction.Structure.GenericURangeLiftBridge
import PartiteConstruction.Structure.GenericUOrderedClosureEquiv

/-!
# Track F — literal bridge between the two U-closedness definitions

The original survey requires a U-closed *range*, while the generic function
dictionary uses output lifting over a root from the source. PR #581 proves
the original range ↔ lifting equivalence. The two tuple implementations
in #581 and #563 expand to exactly the same Fin-cast/snoc expression.

This file connects those now-jointly-present interfaces without assuming
coherence of a target, irreducibility of B, or a finite language.
-/

namespace StructuralRamsey
universe u v w
namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- The input of the nonredundant functional dictionary is exactly the
published source-fibre lifting property, not a stronger closure condition. -/
theorem isUClosedEmbedding_iff_lift
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    IsUClosedEmbedding A B U hU e ↔
      IsUClosedEmbeddingLift A B U hU e := by
  exact Iff.rfl

/-- Missing semantic endgame: the source-fibre predicate in the generic
functional dictionary is LITERALLY the original range-set U-closedness
for induced relational embeddings. -/
theorem isUClosedEmbedding_iff_range
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    IsUClosedEmbedding A B U hU e ↔
      IsUClosedEmbeddingRange U hU e := by
  exact (isUClosedEmbedding_iff_lift U hU e).trans
    (isUClosedEmbeddingRange_iff_lift U hU e).symm

end RelStructure
end StructuralRamsey

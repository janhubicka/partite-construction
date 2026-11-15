import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019
import PartiteConstruction.Functional.TrackCOptionIrredNative

/-!
# Track C: original rich irreducibility survives restoring unary parts

The actual final corrected 2019 tagged source has independent unary
part predicates; its original partial decoder is the UNLABELLED reduct
of the fully part-labelled decoder, with the exact same functions.

Closed-free irreducibility in the unlabelled genuine partial language
implies closed-free irreducibility in ANY corresponding part-labelled
expansion: a closed cover in the richer language is also closed in
the reduct, and relation/function input localization in the richer
language restricts to the original symbols. This uses no fabricated
canonical part map or extra vertices, and keeps some(empty) active.

The direction is sufficient for the rich actual U-test bridge. The
reverse direction requires an additional localization argument for
the added predicates (automatic for unary parts), and is not asserted.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v}
variable {V : Type w}

/-- For an arbitrary partial structure in the language with unary
part predicates, closed-free irreducibility of the ORIGINAL-language
reduct implies it for the expanded structure on the SAME carrier.

No finiteness, positive arity, partial-domain roundtrip, part
normality, or chosen vertex-part function is needed. -/
theorem IsOptionClosedFreeIrreducible.of_originalLanguageReduct
    (A : PartialSetStructure (L.withParts Parts) V)
    (hOriginal :
      A.originalLanguageReduct.IsOptionClosedFreeIrreducible) :
    A.IsOptionClosedFreeIrreducible := by
  intro S T hS hT hCover hRelations hDefined
  have hClosedOriginal
      (Q : Set V) (hQ : A.IsClosed Q) :
      A.originalLanguageReduct.IsClosed Q := by
    intro F xs U hArgs hVal
    exact hQ (ULift.up F) xs U hArgs hVal
  have hRelationsOriginal :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        A.originalLanguageReduct.rel R xs →
        (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T) := by
    intro R xs hRel
    exact hRelations (.inl (ULift.up R)) xs hRel
  have hDefinedOriginal :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
        (U : Set V),
        A.originalLanguageReduct.func F xs = some U →
        (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T) := by
    intro F xs U hVal
    exact hDefined (ULift.up F) xs U hVal
  exact hOriginal S T
    (hClosedOriginal S hS)
    (hClosedOriginal T hT)
    hCover hRelationsOriginal hDefinedOriginal

end StructuralRamsey.PartialSetStructure

import PartiteConstruction.Functional.TrackEExactNativeIrreducibleToTaggedU2019
import PartiteConstruction.Functional.TrackEInternalTaggedBCopyNativeDescent2019
import PartiteConstruction.Functional.PublishedSparseningTarget

/-!
# Track E: ALL native irreducibles obtain INTERNAL full B-copies

The exact native-to-tagged test bridge (parent Track E PR) supplies
intrinsic U-closedness and U-irreducibility of the SAME tested S.
The verified internal tagged-to-native descent (#705) then gives
the FULL internal original native B-copy containing S. The conclusion
is the ORIGINAL property (3) predicate Structure.IrreduciblesExtendTo,
not an external B-test map or a closed-tagged-test-only approximation.
No class H membership or strict full-native B-tree is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {X V : Type v}

/-- Original native full-function clause (3), on EVERY function-closed
and native irreducible exact substructure of the actual final decoder.
All hypotheses concern one selected noncanonical tagged source C. -/
theorem wholeMaskCovered_internalTaggedB_to_allNativeIrreducibles
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L X) [Finite X]
    (basePart : X → P)
    (hTrans : FibreTransversal Base basePart)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    {K : StructureClass
      (L := (L.withParts P).wholeMaskTagLanguage P)}
    (hBaseK : K (wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hHer : ClosedUHereditary K
      ((L.withParts P).wholeMaskClosureRules P))
    (hKIrr : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      K Test → Test.Irreducible)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hInternal :
      IrreduciblesExtendTo
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)) C) :
    Structure.IrreduciblesExtendTo
      Base.collapseDomain (wholeMaskOriginalDecode C).collapseDomain := by
  intro S hS hNativeIrred
  obtain ⟨hSClosed, hSUIrred⟩ :=
    wholeMaskCovered_exactNativeIrred_to_closedTaggedUIrred
      C Base basePart hC hPos hCover S hS hNativeIrred
  exact wholeMaskCovered_internalTaggedB_to_native_of_closedUIrred
    (K := K) C Base basePart hTrans hC hPos
    hBaseK hHer hKIrr hCover hInternal S hSClosed hSUIrred

end StructuralRamsey.RelStructure

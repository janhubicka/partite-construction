import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.WholeMaskTagArrow2019

/-!
# Fully part-labelled genuine partial structures satisfy 2019 U-closure

Apply the verified genuine Option(Set) whole-mask dictionary AFTER
adjoining unary vertex part predicates to the source language.
This encodes actual part preservation in FULL embeddings, even for
isolated vertices; it does not change functions or their values.

The complete-mask tagged expanded source is precisely U-CLOSED, and
its 2019 USize on an EXACT weak induced subset equals the original
whole-fibre partial-function minimum generator rank on the SAME
subset S. No ambient generated hull is counted in place of S.

This is the native source interface for the verified 2019 two-pass
profile construction, with arbitrary transversal set-valued fibres,
repeated input arguments and genuinely defined-empty operations.
Positive primitive arity is required by the 2019 closure root rule.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- The original vertex labels are unary source predicates *inside*
the OLD graph before the U-closure-root tags are introduced. -/
def withPartsWholeMaskTag
    (A : PartialSetStructure L V) (part : V → P) :
    RelStructure ((L.withParts P).wholeMaskTagLanguage P) V :=
  wholeMaskTagExpansion ((A.withParts part).wholeMaskPatternGraph part)

/-- Canonical part-labelled genuinely partial sources have exactly
the 2019 U-closedness required for the initial and second partite
passes, with no auxiliary assumption that the original operations
were total or that empty values are undefined. -/
theorem withPartsWholeMaskTag_isUClosed
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part) :
    IsUClosed ((L.withParts P).wholeMaskClosureRules P)
      (withPartsWholeMaskTag A part) := by
  exact (A.withParts part).wholeMaskTagExpansion_isUClosed
    part ((A.withParts_fibreTransversal_iff part).mpr hTrans)

/-- The exact weak-test numerical invariant: adding unary part
predicates, then complete OLD domain/value masks and full-root tags
DOES NOT CHANGE the intrinsic number of generators of S.

The USize on the right is computed in the relational structure
induced on precisely the original carrier S, not its larger ambient
closure. -/
theorem withPartsWholeMaskTag_exactWeakUSize
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P)
    (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) [Fintype S] (n : ℕ) :
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
      USize ((L.withParts P).wholeMaskClosureRules P)
        ((withPartsWholeMaskTag A part).induce S) ≤ n := by
  calc
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
        (wholeWeakInduce (A.withParts part) S).GeneratedByAtMost n :=
      (A.withParts_wholeWeak_generatedByAtMost_iff part S n).symm
    _ ↔ USize ((L.withParts P).wholeMaskClosureRules P)
          ((withPartsWholeMaskTag A part).induce S) ≤ n :=
      (A.withParts part).wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
        part (hPos.withParts) ((A.withParts_fibreTransversal_iff part).mpr hTrans)
        S n

end StructuralRamsey.PartialSetStructure

import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.WholeMaskDecodedOriginalPartialProjection2019

/-!
# True original-2019 partial projection from the final decoded B-covered picture

The verified 2019 two-pass generated-profile construction produces a
FINAL U-closed tagged relational picture C, with actual protected closed
B-copy coverage and a positive homomorphism to the canonical tagged
relational representation of a genuine partial-function control.

The final decoder already recovers Option(Set) partial values and a unique
vertex part from C. A positive TAGGED relational homomorphism to a
CANONICAL tagged genuine target is enough to recover an original-2019
source-defined partial homomorphism of the decoded actual functions:
each defined entire source fibre maps to exactly the entire control
fibre, and an undefined source input is not required to remain undefined.
Defined-empty is preserved as defined-empty.

The same tagged homomorphism preserves the OLD unary part predicate
holding at each final vertex. Thus the recovered map preserves the
actual vertex part maps, including isolated vertices.

This result requires no intermediate strict functional B-tree completion,
no reflection of source-undefined domains and no enlargement of any
weak source test or projected generator image. It is directly reusable
in the endgame of the verified two-pass 2019 construction.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

/-- The positive control projection of a FINAL canonical-B-covered
U-closed tagged 2019 picture gives a genuine original-partial
homomorphism into the original functional control, while preserving
the actual recovered vertex parts.

The control itself is canonical; the final source C need NOT be its
own canonical tagging before invoking protected B-coverage. -/
theorem wholeMaskOriginalDecode_originalPartialControl_of_tagHom
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (Target : PartialSetStructure L X) (targetPart : X → P)
    (f : V → X)
    (hTag : C.IsHomomorphism
      (wholeMaskTagExpansion
        ((Target.withParts targetPart).wholeMaskPatternGraph targetPart)) f) :
    IsOriginalPartialHomomorphism
      (wholeMaskOriginalDecode C) Target f ∧
    (∀ x : V,
      targetPart (f x) =
        wholeMaskCoveredPart C Base basePart hC hCover x) := by
  classical
  have hOld : (wholeMaskTagReduct C).IsHomomorphism
      ((Target.withParts targetPart).wholeMaskPatternGraph targetPart) f := by
    intro R xs hR
    exact hTag (.inl R) xs hR
  have hPartialPlus :
      IsOriginalPartialHomomorphism
        ((wholeMaskTagReduct C).wholeMaskPartialDecode)
        (Target.withParts targetPart) f :=
    wholeMaskPartialDecode_originalPartial_of_covered_oldHom
      C (Base.withParts basePart) basePart hC
      (hPos.withParts) hCover
      (Target.withParts targetPart) targetPart f hOld
  constructor
  · constructor
    · intro R xs hRel
      exact hPartialPlus.1 (.inl (ULift.up R)) xs hRel
    · intro F xs U hValue
      exact hPartialPlus.2 (ULift.up F) xs U hValue
  · intro x
    have hVertex : WholeMaskVertexPartHolds C x
        (wholeMaskCoveredPart C Base basePart hC hCover x) :=
      wholeMaskCoveredPart_holds C Base basePart hC hCover x
    have hImage : (wholeMaskTagExpansion
        ((Target.withParts targetPart).wholeMaskPatternGraph targetPart)).rel
        (.inl (.inl (.inr
          (wholeMaskCoveredPart C Base basePart hC hCover x))))
        (f ∘ (fun _ : Fin 1 => x)) :=
      hTag (.inl (.inl (.inr
        (wholeMaskCoveredPart C Base basePart hC hCover x))))
        (fun _ : Fin 1 => x) hVertex
    exact hImage

end StructuralRamsey.PartialSetStructure

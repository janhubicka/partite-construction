import PartiteConstruction.Functional.WholeMaskCoveredExactWeakLocalMap2019
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019

/-!
# The exact 2019 tagged weak local completion map is genuinely functional

The checked generated-profile two-pass proof produces a positive
relation-preserving map from C.induce S into a tagged K-completion.
If that K-member is represented by a canonical whole-mask tagged
genuinely partial-function target, then a map from the exact induced
tagged source gives a genuine original-2019 partial homomorphism from
the true weak decoded functional source on the SAME S.

Crucially, C need NOT be a canonical tagged graph of its decoded
functions. Complete OLD output witnesses in C are unique by final
B-copy coverage. If a weak decoded source value survives on S, its
complete OLD tuple lies inside S and is carried by the positive
tagged local homomorphism into the canonical target.

The actual recovered unary part of every original source vertex
is also preserved, because unary part predicates are among the OLD
relations and the target is canonical. No closure of S is taken and
no undefined source function input is required to stay undefined.

This discharges the map-SEMANTICS part of local K-completions.
The class hypothesis that an arbitrary K-member is canonically
representable as a genuine functional target remains independent.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

/-- A local OLD/tagged homomorphism from the ORIGINAL exact weak
vertex set S of a final B-covered U-closed relational picture into a
CANONICAL genuine tagged target yields an original-partial genuine
function homomorphism of the true whole-fibre weak source on S.

The map also preserves each recovered unary vertex part, including
isolated vertices. Intermediate C is not assumed canonical. -/
theorem wholeMaskOriginalDecode_weak_originalPartial_of_taggedLocalHom
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (S : Set V)
    (Target : PartialSetStructure L X) (targetPart : X → P)
    (f : S → X)
    (hTagged : (C.induce S).IsHomomorphism
      (wholeMaskTagExpansion
        ((Target.withParts targetPart).wholeMaskPatternGraph targetPart)) f) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce (wholeMaskOriginalDecode C) S)
      Target f ∧
    (∀ x : S,
      targetPart (f x) =
        wholeMaskCoveredPart C Base basePart hC hCover x.1) := by
  classical
  have hOld :
      ((wholeMaskTagReduct C).induce S).IsHomomorphism
        ((Target.withParts targetPart).wholeMaskPatternGraph targetPart) f := by
    intro R xs hR
    exact hTagged (.inl R) xs hR
  have hPartialPlus : IsOriginalPartialHomomorphism
      (wholeWeakInduce
        ((wholeMaskTagReduct C).wholeMaskPartialDecode) S)
      (Target.withParts targetPart) f :=
    wholeMaskPartialDecode_weak_originalPartial_of_coveredOldHom
      C (Base.withParts basePart) basePart hC (hPos.withParts)
      hCover S (Target.withParts targetPart) targetPart f hOld
  constructor
  · constructor
    · intro R xs hR
      exact hPartialPlus.1 (.inl (ULift.up R)) xs hR
    · intro F xs U hU
      exact hPartialPlus.2 (ULift.up F) xs U hU
  · intro x
    have hPartSource : WholeMaskVertexPartHolds C x.1
        (wholeMaskCoveredPart C Base basePart hC hCover x.1) :=
      wholeMaskCoveredPart_holds C Base basePart hC hCover x.1
    have hPartLocal : (C.induce S).rel
        (.inl (.inl (.inr
          (wholeMaskCoveredPart C Base basePart hC hCover x.1))))
        (fun _ : Fin 1 => x) := hPartSource
    have hPartTarget :=
      hTagged (.inl (.inl (.inr
        (wholeMaskCoveredPart C Base basePart hC hCover x.1))))
        (fun _ : Fin 1 => x) hPartLocal
    exact hPartTarget

end StructuralRamsey.PartialSetStructure

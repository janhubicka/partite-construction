import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.WholeMaskRecoveredPartiteArrow2019
import PartiteConstruction.Functional.WholeMaskTagArrow2019

/-!
# 2019 final U-closed B-covered Picture yields a TRUE partial partite Ramsey arrow

The verified 2019 two-pass construction returns a RELATIONAL final
U-closed tagged Picture. If the final closed U-irreducible tests have
actual full embeddings into canonical tagged B, it decodes into a
genuinely partial Option(Set) structure whose *actual* vertex part map
is recovered from unary part predicates.

This file composes two independently verified ingredients:
  * full OLD canonical A/B relational embeddings of the final target
    become FULL and part-preserving genuine partial embeddings on
    exactly the original vertices (WholeMaskCoveredFunctionalTarget);
  * a relational Ramsey arrow transfers through these SAME vertex-map
    recoveries (WholeMaskRecoveredPartiteArrow).

Neither the source nor the target weak test is replaced by its
ambient closed hull; intermediate relational sparsening targets do
not need to decode. The target-side part function and complete
Option(Set) fibres are reconstructed ONLY at the final closed stage.

Assume positive function input arities (nullary output synchronization
is independent). The remaining global task is to preserve the actual
B-copy coverage certificate in the *statement* of the two-pass sparse
witness; its existing checked proof already constructs this data.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X Y : Type v}

/-- A final U-closed tagged target with genuine canonical B-copy
coverage turns its OLD complete-mask Ramsey arrow directly into a
TRUE part-preserving genuinely partial Option(Set) Ramsey arrow.
No auxiliary "copy recovery" oracle remains. -/
theorem coveredWholeMask_partPreservingArrow_of_old
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (B : PartialSetStructure L W) [Finite W]
    (partB : W → P) (hTransB : FibreTransversal B partB)
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X)
    (Base : PartialSetStructure L Y) (basePart : Y → P)
    (hClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (κ : Type*)
    (hArrow : StructuralRamsey.Arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      (wholeMaskTagReduct C) κ) :
    PartPreservingArrow A partA B partB
      (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C Base basePart hClosed hCover) κ := by
  let recoverA (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) (wholeMaskTagReduct C)) :
      PartPreservingEmbedding A partA (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C Base basePart hClosed hCover) :=
    Embedding.ofCoveredPartiteWholeMaskOld
      A partA hTransA C Base basePart hClosed hPos hCover f
  let recoverB (f : RelStructure.Embedding
      (withPartsWholeMaskOld B partB) (wholeMaskTagReduct C)) :
      PartPreservingEmbedding B partB (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C Base basePart hClosed hCover) :=
    Embedding.ofCoveredPartiteWholeMaskOld
      B partB hTransB C Base basePart hClosed hPos hCover f
  exact partPreservingArrow_of_relational_old_covered
    A partA B partB
    (wholeMaskOriginalDecode C)
    (wholeMaskCoveredPart C Base basePart hClosed hCover)
    (wholeMaskTagReduct C) κ hArrow
    recoverA recoverB
    (fun f x => by
      exact Embedding.ofCoveredPartiteWholeMaskOld_apply
        A partA hTransA C Base basePart hClosed hPos hCover f x)
    (fun f x => by
      exact Embedding.ofCoveredPartiteWholeMaskOld_apply
        B partB hTransB C Base basePart hClosed hPos hCover f x)

/-- Same final theorem starting directly from a Ramsey arrow in the
FULL-ROOT TAGGED 2019 language supplied by the second closed Picture
pass. The target is NOT required to be the canonical tagging of its
OWN OLD reduct. -/
theorem coveredWholeMask_partPreservingArrow_of_tagged
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (B : PartialSetStructure L W) [Finite W]
    (partB : W → P) (hTransB : FibreTransversal B partB)
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X)
    (Base : PartialSetStructure L Y) (basePart : Y → P)
    (hClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (κ : Type*)
    (hArrow : StructuralRamsey.Arrow
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      (wholeMaskTagExpansion (withPartsWholeMaskOld B partB))
      C κ) :
    PartPreservingArrow A partA B partB
      (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C Base basePart hClosed hCover) κ := by
  have hOld : StructuralRamsey.Arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      (wholeMaskTagReduct C) κ :=
    wholeMaskTag_forget_arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB) C κ hArrow
  exact coveredWholeMask_partPreservingArrow_of_old
    A partA hTransA B partB hTransB
    C Base basePart hClosed hPos hCover κ hOld

end StructuralRamsey.PartialSetStructure

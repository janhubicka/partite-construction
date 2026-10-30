import PartiteConstruction.Functional.WholeMaskCanonicalEmbeddingInverse2019
import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019

/-!
# Faithfulness of the whole-mask tagged genuine partial-function presentation

A canonical OLD complete-mask graph with unary vertex parts determines
the ENTIRE genuinely partial Option(Set) structure and every vertex's
part label. The tags add information but do not erase the OLD relations.
Thus equality of two canonical tagged presentations on the SAME carrier
implies equality of the original functions, primitive relations and
part maps. This includes defined-empty versus undefined, repeated
primitive inputs, isolated vertices and nullaries.

This is the exact class-membership reflection needed when defining a
relational K-class as canonical images of an original functional class:
a K-member represented by a target (A,p) cannot secretly represent
a different (B,q). The proof uses the already checked canonical
partial-function decoding theorem, not an assumption about K.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Equal canonical full-tagged descriptions of partite genuine
Option(Set) structures have IDENTICAL vertex part maps and functions
on the same original carrier. -/
theorem withPartsWholeMaskTagged_injective
    (A B : PartialSetStructure L V) [Finite V]
    (partA partB : V → P)
    (hTrA : FibreTransversal A partA)
    (hTrB : FibreTransversal B partB)
    (hEq :
      wholeMaskTagExpansion (withPartsWholeMaskOld A partA) =
      wholeMaskTagExpansion (withPartsWholeMaskOld B partB)) :
    A = B ∧ partA = partB := by
  classical
  have hOld : withPartsWholeMaskOld A partA =
      withPartsWholeMaskOld B partB := by
    apply RelStructure.rel_injective
    funext R xs
    exact congrArg
      (fun E : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V =>
        E.rel (.inl R) xs) hEq
  have hTransPlusA : FibreTransversal (A.withParts partA) partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTrA
  have hTransPlusB : FibreTransversal (B.withParts partB) partB :=
    (B.withParts_fibreTransversal_iff partB).mpr hTrB
  have hEqDecoded :
      (withPartsWholeMaskOld A partA).wholeMaskPartialDecode =
      (withPartsWholeMaskOld B partB).wholeMaskPartialDecode :=
    congrArg
      (fun E : RelStructure ((L.withParts P).wholeMaskPatternLanguage P) V =>
        E.wholeMaskPartialDecode) hOld
  have hPlus : A.withParts partA = B.withParts partB := by
    calc
      A.withParts partA =
          (withPartsWholeMaskOld A partA).wholeMaskPartialDecode :=
        ((A.withParts partA).wholeMaskPartialDecode_canonical_eq
          partA hTransPlusA).symm
      _ = (withPartsWholeMaskOld B partB).wholeMaskPartialDecode :=
        hEqDecoded
      _ = B.withParts partB :=
        (B.withParts partB).wholeMaskPartialDecode_canonical_eq
          partB hTransPlusB
  have hRel (R : L.RelSymbol) (xs : Fin (L.relArity R) → V) :
      A.rel R xs = B.rel R xs :=
    congrArg
      (fun E : PartialSetStructure (L.withParts P) V =>
        E.rel (.inl (ULift.up R)) xs) hPlus
  have hFunc (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) :
      A.func F xs = B.func F xs :=
    congrArg
      (fun E : PartialSetStructure (L.withParts P) V =>
        E.func (ULift.up F) xs) hPlus
  have hAB : A = B := by
    cases A with
    | mk relA funcA =>
      cases B with
      | mk relB funcB =>
        have hr : relA = relB := by
          funext R xs
          exact hRel R xs
        have hf : funcA = funcB := by
          funext F xs
          exact hFunc F xs
        cases hr
        cases hf
        rfl
  have hParts : partA = partB := by
    funext x
    have hPart : (B.withParts partB).rel (.inr (partA x))
        (fun _ : Fin 1 => x) := by
      have hPartA : (A.withParts partA).rel (.inr (partA x))
          (fun _ : Fin 1 => x) := rfl
      rw [hPlus] at hPartA
      exact hPartA
    exact hPart.symm
  exact ⟨hAB, hParts⟩

end StructuralRamsey.PartialSetStructure

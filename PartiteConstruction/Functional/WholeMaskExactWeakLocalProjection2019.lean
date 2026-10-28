import PartiteConstruction.Functional.WholeMaskExactWeakDecode2019
import PartiteConstruction.Functional.WholeMaskDecodedOriginalPartialProjection2019

/-!
# The 2019 exact induced OLD test maps to a genuine weak partial-function test

The verified two-pass sparsening lemma produces a positive relational
homomorphism-embedding of the AMBIENT OLD graph induced on the exact
weak carrier S into a finite K-completion.

If the completion has a CANONICAL genuine partial-function target
interpretation, the OLD complete-value relational homomorphism is
enough to recover precisely the original-2019 source-defined
partial homomorphism of the true weak function restriction to S.

The crucial input is the exact semantic equality from
WholeMaskExactWeakDecode2019: decoding the induced OLD graph yields
the whole-fibre weak partial function, even though the persistent
ambient OLD domain predicates can differ from the weak domain.

Thus the standard 2019 U-closed local completion maps translate to
genuine partial-function weak tests without taking closure of S.
No full/domain-reflecting projection is required, and defined-empty
is preserved as a genuinely defined empty value.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w} {W : Type z}

/-- A positive OLD complete-value relational homomorphism from the
exact INDUCED AMBIENT test to a canonical genuine partial completion
induces an original-2019 genuinely partial homomorphism on the true
whole-fibre weak restriction of exactly S.

This holds for repeated primitive input coordinates, arbitrary
transversal multivalued outputs and defined-empty operations, with
no change in test cardinality and no reflection of undefinedness. -/
theorem wholeWeakInduce_originalPartial_of_inducedOldHom
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V)
    (Target : PartialSetStructure L W) (targetPart : W → P)
    (f : S → W)
    (hOld : ((A.wholeMaskPatternGraph part).induce S).IsHomomorphism
      (Target.wholeMaskPatternGraph targetPart) f) :
    IsOriginalPartialHomomorphism (wholeWeakInduce A S) Target f := by
  classical
  let Old := (A.wholeMaskPatternGraph part).induce S
  let Weak := wholeWeakInduce A S
  have hTransWeak : FibreTransversal Weak (part ∘ Subtype.val) :=
    FibreTransversal.wholeWeakInduce A part hTrans S
  have hUnique (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → S) (U T : Set S)
      (hU : HasWholeMaskValue Old F xs U)
      (hT : HasWholeMaskValue Old F xs T) : U = T := by
    have hUw : HasWholeMaskValue
        (Weak.wholeMaskPatternGraph (part ∘ Subtype.val)) F xs U :=
      (A.wholeMaskValue_weak_iff_induced part S F xs U).mpr hU
    have hTw : HasWholeMaskValue
        (Weak.wholeMaskPatternGraph (part ∘ Subtype.val)) F xs T :=
      (A.wholeMaskValue_weak_iff_induced part S F xs T).mpr hT
    have hu : Weak.func F xs = some U :=
      (Weak.hasWholeMaskValue_iff_source_func_some
        (part ∘ Subtype.val) hTransWeak F xs U).mp hUw
    have ht : Weak.func F xs = some T :=
      (Weak.hasWholeMaskValue_iff_source_func_some
        (part ∘ Subtype.val) hTransWeak F xs T).mp hTw
    exact Option.some.inj (hu.symm.trans ht)
  have hDecoded : IsOriginalPartialHomomorphism
      Old.wholeMaskPartialDecode Target f :=
    wholeMaskPartialDecode_originalPartial_of_oldHom
      Old Target targetPart f hUnique hOld
  constructor
  · intro R xs hRel
    exact hDecoded.1 R xs hRel
  · intro F xs U hValue
    have hOldValue : Old.wholeMaskPartialDecode.func F xs = some U := by
      rw [A.wholeMaskPartialDecode_induced_func_eq_wholeWeak
        part hTrans S F xs]
      exact hValue
    exact hDecoded.2 F xs U hOldValue

end StructuralRamsey.PartialSetStructure

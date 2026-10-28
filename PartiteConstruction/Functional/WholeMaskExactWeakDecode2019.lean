import PartiteConstruction.Functional.WholeMaskCanonicalPartialRoundTrip2019
import PartiteConstruction.Structure.PartialSetFunctionsWholePartWeakDictionary
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns

/-!
# Decoding exact OLD induced masks equals whole-fibre weak function restriction

The 2019 proof tests the ORIGINAL weak vertex set S. The OLD
complete-mask language has independent domain masks: inducing to S
retains an active ambient domain even if an output leaves S.
Thus the whole OLD induced structure does not equal the canonical
OLD graph of the weak function substructure.

Instead, these two structures have identical COMPLETE OUTPUT TUPLE
relations. The genuinely partial decoder depends only on those
complete tuple witnesses, so decoding the exact induced OLD
structure agrees with whole-fibre weak restriction.

Defined-empty remains different from undefined, repeated input
coordinates and nullaries are allowed, and no source carrier grows.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Complete OLD whole-value witnesses survive exact weak restriction
exactly when the whole tuple lies in the ambient induced carrier.
No analogous statement is made for persistent OLD domain masks. -/
theorem wholeMaskValue_weak_iff_induced
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (T : Set S) :
    HasWholeMaskValue
      ((wholeWeakInduce A S).wholeMaskPatternGraph
        (part ∘ Subtype.val)) F xs T ↔
    HasWholeMaskValue
      ((A.wholeMaskPatternGraph part).induce S) F xs T := by
  constructor
  · rintro ⟨m,r,hr,q,t,hRel,hArgs,hT⟩
    let p : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
    have hTarget :
        ((A.wholeMaskPatternGraph part).induce S).rel
          (.inr (.inr (p,q))) t :=
      (A.wholeWeakInduce_wholeMaskPatternGraph_output_iff
        part S p q t).mp hRel
    exact ⟨m,r,hr,q,t,hTarget,hArgs,hT⟩
  · rintro ⟨m,r,hr,q,t,hRel,hArgs,hT⟩
    let p : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
    have hSource :
        ((wholeWeakInduce A S).wholeMaskPatternGraph
          (part ∘ Subtype.val)).rel (.inr (.inr (p,q))) t :=
      (A.wholeWeakInduce_wholeMaskPatternGraph_output_iff
        part S p q t).mpr hRel
    exact ⟨m,r,hr,q,t,hSource,hArgs,hT⟩

/-- Pointwise genuinely partial Option(Set) values decoded from
the exact induced AMBIENT OLD complete-mask relations agree with
the actual whole-fibre weak operation on S. Even when an active
domain mask persists, it cannot produce an artificial defined
empty value without a complete zero-output relation tuple. -/
theorem wholeMaskPartialDecode_induced_func_eq_wholeWeak
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (((A.wholeMaskPatternGraph part).induce S).wholeMaskPartialDecode).func
        F xs =
      (wholeWeakInduce A S).func F xs := by
  classical
  let Weak := wholeWeakInduce A S
  let Old := (A.wholeMaskPatternGraph part).induce S
  have hTransWeak : FibreTransversal Weak
      (part ∘ Subtype.val) :=
    FibreTransversal.wholeWeakInduce A part hTrans S
  have hValues (T : Set S) :
      HasWholeMaskValue Old F xs T ↔
        Weak.func F xs = some T := by
    have hWeak : HasWholeMaskValue
        (Weak.wholeMaskPatternGraph (part ∘ Subtype.val)) F xs T ↔
        Weak.func F xs = some T :=
      Weak.hasWholeMaskValue_iff_source_func_some
        (part ∘ Subtype.val) hTransWeak F xs T
    exact (A.wholeMaskValue_weak_iff_induced
      part S F xs T).symm.trans hWeak
  have hUnique (U T : Set S)
      (hU : HasWholeMaskValue Old F xs U)
      (hT : HasWholeMaskValue Old F xs T) : U = T := by
    have hu : Weak.func F xs = some U := (hValues U).mp hU
    have ht : Weak.func F xs = some T := (hValues T).mp hT
    exact Option.some.inj (hu.symm.trans ht)
  change Old.wholeMaskPartialDecode.func F xs = Weak.func F xs
  cases hOrig : Weak.func F xs with
  | none =>
      have hNo : ¬ ∃ T : Set S, HasWholeMaskValue Old F xs T := by
        rintro ⟨T,hT⟩
        have hTVal := (hValues T).mp hT
        rw [hOrig] at hTVal
        cases hTVal
      have hDecoded : Old.wholeMaskPartialDecode.func F xs = none :=
        (Old.wholeMaskPartialDecode_func_none_iff F xs).mpr hNo
      exact hDecoded
  | some T =>
      have hOld : HasWholeMaskValue Old F xs T :=
        (hValues T).mpr hOrig
      have hDecoded : Old.wholeMaskPartialDecode.func F xs = some T :=
        (Old.wholeMaskPartialDecode_func_some_iff F xs hUnique T).mpr hOld
      exact hDecoded

/-- Primitive relations of the decoded induced ambient OLD graph are
the relations of the true weak function restriction, on exactly S. -/
theorem wholeMaskPartialDecode_induced_rel_eq_wholeWeak
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V)
    (R : L.RelSymbol) (xs : Fin (L.relArity R) → S) :
    (((A.wholeMaskPatternGraph part).induce S).wholeMaskPartialDecode).rel
        R xs =
      (wholeWeakInduce A S).rel R xs := rfl

end StructuralRamsey.PartialSetStructure

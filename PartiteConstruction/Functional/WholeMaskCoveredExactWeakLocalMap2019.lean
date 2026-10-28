import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Functional.WholeMaskExactWeakLocalProjection2019

/-!
# From the final covered OLD induced test to an exact genuine weak local map

The verified 2019 two-pass profile sparsening produces a RELATIONAL
homomorphism of the ambient complete-mask OLD graph induced on the
literal weak carrier S. The final OLD graph is not necessarily the
canonical graph of the decoded partial source: old domain masks persist
on S even when the full value lies outside S.

This theorem avoids imposing that false equality. It uses only the
uniqueness of complete value witnesses in the ambient OLD graph,
which is guaranteed by final closed B-copy coverage.

If the genuine whole-fibre weak decoded source F(x) is defined with
complete value U, its ambient decoded input has a complete value T
with T subset S. A complete OLD witness enumerating exactly T
therefore restricts to a relation tuple on the SAME S, since all
output coordinates are in T and all distinct input-root coordinates
are actual primitive input coordinates (surjectivity of the input
pattern). Transport the entire relation through the exact local
OLD homomorphism into the canonical genuine target: the target value
must be precisely the image of U.

This is the direct local K-completion semantic bridge used by the
actual 2019 two-pass proof. Undefined source inputs are not reflected,
and none / some empty stay different. No weak test S is enlarged,
and no strict native functional B-tree target is assumed.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w} {W : Type z}

/-- A positive OLD relational map from the ambient complete-mask
graph induced on exactly S into a canonical genuine partial target
is a genuine original-2019 partial homomorphism on the WHOLE-FIBRE
weak restriction of the ambient decoded source. The ambient OLD
graph itself need NOT be canonical or have correct domain masks;
we only assume uniqueness of entire OLD complete-value witnesses.

This transfers the exact weak local-completion map without taking
a closure hull of S or reflecting undefined source function inputs. -/
theorem wholeMaskPartialDecode_weak_originalPartial_of_inducedOldHom
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (hUnique : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V)
      (U T : Set V),
      HasWholeMaskValue E F xs U →
      HasWholeMaskValue E F xs T → U = T)
    (S : Set V)
    (Target : PartialSetStructure L W) (targetPart : W → P)
    (f : S → W)
    (hOld : (E.induce S).IsHomomorphism
      (Target.wholeMaskPatternGraph targetPart) f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce E.wholeMaskPartialDecode S)
      Target f := by
  classical
  constructor
  · intro R xs hRel
    exact hOld (.inl R) xs hRel
  · intro F xs U hWeak
    have hWeakValue : PartialSetStructure.wholeWeakValue S
        (E.wholeMaskPartialDecode.func F (Subtype.val ∘ xs)) =
          some U := hWeak
    obtain ⟨T, hT, hTS, hUT⟩ :=
      (PartialSetStructure.wholeWeakValue_eq_some_iff S _ U).mp hWeakValue
    have hWitness : HasWholeMaskValue E F (Subtype.val ∘ xs) T :=
      (E.wholeMaskPartialDecode_func_some_iff
        F (Subtype.val ∘ xs)
        (hUnique F (Subtype.val ∘ xs)) T).mp hT
    obtain ⟨m, r, hr, q, t, hRel, hArgs, hTSet⟩ := hWitness
    let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
    have hRoot (i : Fin m) :
        t (Fin.castAdd q.size i) ∈ S := by
      obtain ⟨j, hj⟩ := hr i
      have hx : (Subtype.val ∘ xs) j ∈ S := (xs j).2
      rw [hArgs j] at hx
      simpa only [hj] using hx
    have hOut (j : Fin q.size) :
        t (Fin.natAdd m j) ∈ S := by
      apply hTS
      rw [hTSet]
      exact ⟨j, rfl⟩
    have hAll (k : Fin (m + q.size)) : t k ∈ S :=
      Fin.addCases hRoot hOut k
    let tS : Fin (m + q.size) → S :=
      fun k => ⟨t k, hAll k⟩
    have hRelS : (E.induce S).rel (.inr (.inr (pat,q))) tS :=
      hRel
    have hMapped : (Target.wholeMaskPatternGraph targetPart).rel
        (.inr (.inr (pat,q))) (f ∘ tS) :=
      hOld (.inr (.inr (pat,q))) tS hRelS
    have hTarget : Target.func F
        ((fun i : Fin m => f (tS (Fin.castAdd q.size i))) ∘ r) =
          some (Set.range (fun j : Fin q.size =>
            f (tS (Fin.natAdd m j)))) :=
      hMapped.2.1
    have hInput : ((fun i : Fin m =>
        f (tS (Fin.castAdd q.size i))) ∘ r) = f ∘ xs := by
      funext i
      apply congrArg f
      apply Subtype.ext
      exact (hArgs i).symm
    have hOutput :
        Set.range (fun j : Fin q.size =>
          f (tS (Fin.natAdd m j))) =
        Structure.imageSet f U := by
      rw [hUT]
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        have hIn : (tS (Fin.natAdd m j)).1 ∈ T := by
          change t (Fin.natAdd m j) ∈ T
          rw [hTSet]
          exact ⟨j, rfl⟩
        exact ⟨tS (Fin.natAdd m j), hIn, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hIn : x.1 ∈ T := hx
        rw [hTSet] at hIn
        obtain ⟨j, hj⟩ := hIn
        have hEq : x = tS (Fin.natAdd m j) :=
          Subtype.ext hj.symm
        exact ⟨j, congrArg f hEq.symm⟩
    rw [hInput, hOutput] at hTarget
    exact hTarget

/-- In particular the VERIFIED final canonical-B-covered tagged
source provides the full-value uniqueness hypothesis above, so an
OLD local map of its exact induced weak source immediately becomes
a true source-defined partial map into any canonical completion. -/
theorem wholeMaskPartialDecode_weak_originalPartial_of_coveredOldHom
    {Q : Type w}
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (S : Set V)
    (Target : PartialSetStructure L W) (targetPart : W → P)
    (f : S → W)
    (hOld : ((wholeMaskTagReduct C).induce S).IsHomomorphism
      (Target.wholeMaskPatternGraph targetPart) f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce
        (wholeMaskTagReduct C).wholeMaskPartialDecode S)
      Target f := by
  exact wholeMaskPartialDecode_weak_originalPartial_of_inducedOldHom
    (wholeMaskTagReduct C)
    (fun F xs U T hU hT =>
      wholeMaskValue_unique_of_closed_coverage
        C Base basePart hC hPos hCover F xs U T hU hT)
    S Target targetPart f hOld

end StructuralRamsey.RelStructure

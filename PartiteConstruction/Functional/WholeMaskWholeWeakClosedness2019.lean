import PartiteConstruction.Functional.WholeMaskRelativeClosure2019
import PartiteConstruction.Functional.WholeMaskTagInduce2019
import PartiteConstruction.Functional.TupleEqualityPattern2019
import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Structure.PartialSetFunctionsWholePartRepresent

/-!
# Exact whole-fibre weak closedness in ambient complete-mask tuples

The native weak restriction drops the ENTIRE function application when
any output escapes an arbitrary exact vertex set S. The OLD complete
mask relational graph induced from the AMBIENT source on S has precisely
the surviving complete-value tuples, but retains separately all ambient
domain-mask incidences. Relative closure under the complete-value tuples
therefore agrees with intrinsic function-closedness INSIDE the whole-weak
partial-function structure on the exact carrier S.

The next U-substructure correspondence uses the generic well-formed
2019 full-root tag lemma; root tags and domain masks are never
recomputed from the weak functions.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Intrinsic function-closedness of an exact whole-fibre weak test equals
closure under the AMBIENT OLD complete-value tuples induced on S. -/
theorem wholeWeakIsClosed_iff_inducedWholeMaskTuples
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).IsClosed Q ↔
      IsClosedByWholeMaskTuples
        ((A.wholeMaskPatternGraph part).induce S) Q := by
  classical
  constructor
  · intro hClosed p q t ht hInputs j
    have hVal :
        A.func p.symbol
          ((fun i : Fin p.rootSize =>
            (t (Fin.castAdd q.size i)).1) ∘ p.argMap) =
          some (Set.range (fun k : Fin q.size =>
            (t (Fin.natAdd p.rootSize k)).1)) := ht.2.1
    have hUsub :
        Set.range (fun k : Fin q.size =>
            (t (Fin.natAdd p.rootSize k)).1) ⊆ S := by
      rintro x ⟨k, rfl⟩
      exact (t (Fin.natAdd p.rootSize k)).2
    have hClosedRule :=
      (A.wholeWeakInduce_isClosed_iff S Q).mp hClosed
    exact hClosedRule p.symbol
      ((fun i : Fin p.rootSize => t (Fin.castAdd q.size i)) ∘
        p.argMap)
      (Set.range (fun k : Fin q.size =>
        (t (Fin.natAdd p.rootSize k)).1))
      (fun i => hInputs (p.argMap i))
      hVal hUsub
      (t (Fin.natAdd p.rootSize j))
      ⟨j, rfl⟩
  · intro hMask
    apply (A.wholeWeakInduce_isClosed_iff S Q).mpr
    intro F xs U hInputs hValue hUS y hy
    obtain ⟨q, ys, hRange, hLabels⟩ :=
      A.completeOutputPartGraph_represents_value part hTrans
        F (Subtype.val ∘ xs) U hValue
    obtain ⟨m, r, e, hSurj, hInj, hFact, _⟩ :=
      exists_tuple_equality_pattern_exact (Subtype.val ∘ xs)
    let pat : Language.FunctionInputPattern L :=
      ⟨F, m, r, hSurj⟩
    have hArgs : e ∘ r = Subtype.val ∘ xs := by
      funext i
      exact (hFact i).symm
    let inputS : Fin m → S := fun i =>
      ⟨e i, by
        obtain ⟨k, hk⟩ := hSurj i
        rw [← hk, ← hFact k]
        exact (xs k).2⟩
    let outputS : Fin q.size → S := fun j =>
      ⟨ys j, hUS (by
        rw [← hRange]
        exact ⟨j, rfl⟩)⟩
    let t : Fin (m + q.size) → S := Fin.append inputS outputS
    have hTuple :
        ((A.wholeMaskPatternGraph part).induce S).rel
          (.inr (.inr (pat,q))) t := by
      change
        Function.Injective (fun i : Fin m =>
          (t (Fin.castAdd q.size i)).1) ∧
          A.func F ((fun i : Fin m =>
            (t (Fin.castAdd q.size i)).1) ∘ r) =
            some (Set.range (fun j : Fin q.size =>
              (t (Fin.natAdd m j)).1)) ∧
          (∀ j : Fin q.size,
            part (t (Fin.natAdd m j)).1 = q.label j)
      simp only [t, Fin.append_left, Fin.append_right]
      refine ⟨hInj, ?_, hLabels⟩
      rw [hArgs, hRange]
      exact hValue
    have hRoot : ∀ i : Fin m,
        t (Fin.castAdd q.size i) ∈ Q := by
      intro i
      obtain ⟨k, hk⟩ := hSurj i
      have hEq : inputS i = xs k := by
        apply Subtype.ext
        change e i = (xs k).1
        rw [← hk, ← hFact k]
        rfl
      have hIn : inputS i ∈ Q := by
        rw [hEq]
        exact hInputs k
      simpa only [t, Fin.append_left] using hIn
    have hOutputs : ∀ j : Fin q.size,
        t (Fin.natAdd m j) ∈ Q :=
      hMask pat q t hTuple hRoot
    have hyRange : y.1 ∈ Set.range ys := by
      rw [hRange]
      exact hy
    obtain ⟨j, hj⟩ := hyRange
    have hOutput : outputS j ∈ Q := by
      simpa only [t, Fin.append_right] using hOutputs j
    have hEq : outputS j = y := by
      apply Subtype.ext
      exact hj
    rw [hEq] at hOutput
    exact hOutput

/-- 2019 relative U-closedness of the induced AMBIENT full-mask tagged
source equals genuine intrinsic whole-weak function closedness INSIDE S.
Active mask domains survive from ambient even when weak functions vanish. -/
theorem wholeWeakIsClosed_iff_inducedAmbientTagUSubstructure
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).IsClosed Q ↔
      IsUSubstructure (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S) Q := by
  let E := (A.wholeMaskPatternGraph part).induce S
  have hValid : HasValidCompleteMaskDomains E :=
    (A.wholeMaskPatternGraph_validDomains part).induce S
  have hOld : (wholeWeakInduce A S).IsClosed Q ↔
      IsClosedByWholeMaskTuples E Q :=
    A.wholeWeakIsClosed_iff_inducedWholeMaskTuples part hTrans S Q
  have hTagged : IsClosedByWholeMaskTuples E Q ↔
      IsUSubstructure (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion E) Q :=
    isClosedByWholeMaskTuples_iff_Usubstructure E hValid hPos Q
  have hEq : wholeMaskTagExpansion E =
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S :=
    wholeMaskTagExpansion_induce_eq (A.wholeMaskPatternGraph part) S
  rw [hEq] at hTagged
  exact hOld.trans hTagged

end StructuralRamsey.PartialSetStructure

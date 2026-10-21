import PartiteConstruction.Functional.WholeMaskWholeWeakClosedness2019
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-!
# Exact whole-fibre weak generator ranks equal 2019 USize

The corrected iterated construction measures the number of VERTICES
needed to generate each exact weak test under operations that survive
whole-fibre deletion. It does not count the vertices in a generated
ambient closure hull.

The preceding exact-weak source dictionary equates intrinsic
whole-fibre closed subsets with relative U-substructures of the
AMBIENT 2019 full-root tagged graph induced on exactly S. Taking the
intersection of the same closed supersets equates their closure
operators; minimizing the cardinality of generating subsets then
gives the literal generator-rank/USize correspondence.

This is SOURCE bookkeeping. Arbitrary tagged target completion,
masked-output coherence and strict B-tree targets are still open.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Complete-output weak native closure INSIDE the exact tested carrier
equals relative 2019 U-closure in the ambient tagged structure induced
on that SAME carrier. This is NOT ambient closure of Q in the whole A. -/
theorem wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).functionClosure Q =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S) Q := by
  let Weak := wholeWeakInduce A S
  let Tagged :=
    (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S
  let rules := L.wholeMaskClosureRules P
  have hClosed (T : Set S) :
      Weak.IsClosed T ↔ IsUSubstructure rules Tagged T :=
    A.wholeWeakIsClosed_iff_inducedAmbientTagUSubstructure
      part hPos hTrans S T
  ext x
  change
    (∀ T : Set S, Weak.IsClosed T → Q ⊆ T → x ∈ T) ↔
      (∀ T : Set S,
        IsUSubstructure rules Tagged T → Q ⊆ T → x ∈ T)
  constructor
  · intro h T hT hQT
    exact h T ((hClosed T).mpr hT) hQT
  · intro h T hT hQT
    exact h T ((hClosed T).mp hT) hQT

/-- The exact whole-fibre weak-test intrinsic minimum generator bound
equals 2019 USize of the induced AMBIENT complete-mask source. In
particular the weak test S is not replaced by its larger closed hull. -/
theorem wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) [Fintype S] (n : ℕ) :
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S) ≤ n := by
  let Weak := wholeWeakInduce A S
  let Tagged :=
    (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S
  let rules := L.wholeMaskClosureRules P
  have hGen (T : Set S) :
      Weak.GeneratedBy T ↔ IsUGenerating rules Tagged T := by
    change Weak.functionClosure T = Set.univ ↔
      UClosureHull rules Tagged T = Set.univ
    rw [A.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      part hPos hTrans S T]
  constructor
  · rintro ⟨G, hCard, hGenerate⟩
    have hU : IsUGenerating rules Tagged (↑G : Set S) :=
      (hGen (↑G : Set S)).mp hGenerate
    exact (USize_le_of_generating rules Tagged G hU).trans hCard
  · intro h
    obtain ⟨G, hCard, hU⟩ := USize_spec rules Tagged
    have hBound : G.card ≤ n := by
      rw [hCard]
      exact h
    exact ⟨G, hBound, (hGen (↑G : Set S)).mpr hU⟩

end StructuralRamsey.PartialSetStructure

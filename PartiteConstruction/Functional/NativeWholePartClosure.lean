import PartiteConstruction.Structure.PartialSetFunctionsWholePartWeakDictionary
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.Basic

/-!
# Finite whole-fibre closure dictionary on actual native partite systems

The existing native Hales--Jewett construction uses set-valued functions
with an empty set standing for an undefined application. Exposing exactly
its nonempty fibres as partial values preserves output-part transversality.

Consequently the finite complete-value source dictionary applies directly
to each actual native partite system, including its exact weak tests. This
does NOT convert arbitrary defined-empty partial structures to the native
representation, nor construct strict functional B-tree target completions.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- The faithful nonempty-defined partial presentation of a native
transversal partite system has transversal partial output fibres. -/
theorem System.toNonemptyPartial_fibreTransversal
    (B : System L P V) :
    FibreTransversal B.toStructure.toNonemptyPartial B.part := by
  classical
  intro F xs U hValue y hy z hz hPart
  change
    (if (B.toStructure.func F xs).Nonempty then
      some (B.toStructure.func F xs) else none) = some U at hValue
  by_cases hNonempty : (B.toStructure.func F xs).Nonempty
  · have hSome : some (B.toStructure.func F xs) = some U := by
      simpa [hNonempty] using hValue
    have hEq : B.toStructure.func F xs = U :=
      Option.some.inj hSome
    exact B.funcTransversal F xs y z
      (by rw [hEq]; exact hy)
      (by rw [hEq]; exact hz)
      hPart
  · simp [hNonempty] at hValue

/-- The whole-weak native partial structure and the induced AMBIENT
finite complete-value graph have the same vertex-closed subsets. -/
theorem System.wholeWeakIsClosed_iff_completePartGraph
    (B : System L P V) [Finite V]
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce B.toStructure.toNonemptyPartial S).IsClosed Q ↔
      IsClosedByCompleteParts
        ((completeOutputPartGraph B.toStructure.toNonemptyPartial B.part).induce S) Q :=
  wholeWeakInduce_isClosed_iff_inducedCompletePartGraph
    B.toStructure.toNonemptyPartial B.part
    B.toNonemptyPartial_fibreTransversal S Q

/-- Exact weak native vertex closure agrees with the finite complete-part
relational closure on the same original weak tested vertices. -/
theorem System.wholeWeakFunctionClosure_eq_completePartHull
    (B : System L P V) [Finite V]
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q =
      completePartClosureHull
        ((completeOutputPartGraph B.toStructure.toNonemptyPartial B.part).induce S) Q :=
  wholeWeakInduce_functionClosure_eq_inducedCompletePartHull
    B.toStructure.toNonemptyPartial B.part
    B.toNonemptyPartial_fibreTransversal S Q

/-- The literal whole-fibre weak generator-size invariant for the actual
native partite system is the finite complete-value induced graph invariant.
The original S is never replaced by its ambient function closure. -/
theorem System.wholeWeakGeneratedByAtMost_iff_completePartGraph
    (B : System L P V) [Finite V]
    (S : Set V) (n : ℕ) :
    (wholeWeakInduce B.toStructure.toNonemptyPartial S).GeneratedByAtMost n ↔
      CompletePartGeneratedByAtMost
        ((completeOutputPartGraph B.toStructure.toNonemptyPartial B.part).induce S) n :=
  wholeWeakInduce_generatedByAtMost_iff_inducedCompletePartGraph
    B.toStructure.toNonemptyPartial B.part
    B.toNonemptyPartial_fibreTransversal S n

end StructuralRamsey.FunctionalPartite

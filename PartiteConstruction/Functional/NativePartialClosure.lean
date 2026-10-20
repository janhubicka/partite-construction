import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.ClosedGeneratorRank

/-!
# Vertex closure in the native nonempty-defined partial presentation

The native set-valued structure is recovered exactly after exposing its
nonempty-defined domain and then forgetting that independent domain bit.
Hence its vertex closedness, closure operator, and generator bounds agree
with the partial presentation. This does not identify arbitrary partial
structures containing defined-empty values with the native construction.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The native conversion records exactly the native incidence fibres. -/
@[simp] theorem toNonemptyPartial_collapseDomain (A : Structure L V) :
    A.toNonemptyPartial.collapseDomain = A := by
  classical
  cases A with
  | mk rel func =>
      change Structure.mk rel _ = Structure.mk rel func
      congr 1
      funext F x
      change (if (func F x).Nonempty then some (func F x) else none).getD ∅ =
        func F x
      by_cases h : (func F x).Nonempty
      · simp [h]
      · have hEmpty : func F x = ∅ := by
          ext y
          constructor
          · intro hy
            exact (h ⟨y, hy⟩).elim
          · intro hy
            exact hy.elim
        simp [h, hEmpty]

theorem toNonemptyPartial_isClosed_iff
    (A : Structure L V) (S : Set V) :
    A.toNonemptyPartial.IsClosed S ↔ A.IsClosed S := by
  rw [PartialSetStructure.isClosed_iff_collapseDomain_isClosed,
    toNonemptyPartial_collapseDomain]

theorem toNonemptyPartial_functionClosure
    (A : Structure L V) (S : Set V) :
    A.toNonemptyPartial.functionClosure S = A.functionClosure S := by
  rw [PartialSetStructure.functionClosure, toNonemptyPartial_collapseDomain]

theorem toNonemptyPartial_generatedBy_iff
    (A : Structure L V) (S : Set V) :
    A.toNonemptyPartial.GeneratedBy S ↔ A.GeneratedBy S := by
  change A.toNonemptyPartial.functionClosure S = Set.univ ↔
    A.functionClosure S = Set.univ
  rw [A.toNonemptyPartial_functionClosure S]

theorem toNonemptyPartial_generatedByAtMost_iff
    (A : Structure L V) (n : ℕ) :
    A.toNonemptyPartial.GeneratedByAtMost n ↔ A.GeneratedByAtMost n := by
  constructor
  · rintro ⟨S, hCard, hGen⟩
    exact ⟨S, hCard, (A.toNonemptyPartial_generatedBy_iff (↑S : Set V)).mp hGen⟩
  · rintro ⟨S, hCard, hGen⟩
    exact ⟨S, hCard, (A.toNonemptyPartial_generatedBy_iff (↑S : Set V)).mpr hGen⟩

end StructuralRamsey.Structure

import PartiteConstruction.Structure.PartialSetFunctionsWholePartClosure
import PartiteConstruction.Functional.PatternLanguageFinite

/-!
# Exact whole-weak tests and the finite complete-value source closure

Whole-fibre weak restriction preserves output-part transversality, and its
finite complete-value relational presentation is literally the induced
ambient presentation on the SAME tested vertices. Combining these facts
with the source closure/rank dictionary proves the exact weak analogue:
intrinsic function closure and generator bounds on S match those of the
induced ambient finite complete-value relations.

This does NOT yet identify the latter with 2019 USize: fresh irreducible
full root-pattern tags and their active domain clauses remain necessary.
There is no target completion oracle or enlargement of the tested set.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Whole-fibre deletion keeps every surviving complete function value
transversal to the inherited part map, including defined-empty values. -/
theorem FibreTransversal.wholeWeakInduce
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part) (S : Set V) :
    FibreTransversal (wholeWeakInduce A S)
      (part ∘ Subtype.val) := by
  intro F xs T hValue y hy z hz hPart
  change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) = some T at hValue
  obtain ⟨U, hU, _, hT⟩ :=
    (wholeWeakValue_eq_some_iff S _ T).mp hValue
  have hyU : y.1 ∈ U := by
    rw [hT] at hy
    exact hy
  have hzU : z.1 ∈ U := by
    rw [hT] at hz
    exact hz
  apply Subtype.ext
  exact hTrans F (Subtype.val ∘ xs) U hU
    y.1 hyU z.1 hzU hPart

/-- The full finite complete-value relational structure on the weak
carrier equals the ambient relational induced structure there. This
equality is an identity of relations, not merely a homomorphism. -/
theorem wholeWeakInduce_completeOutputPartGraph_eq
    (A : PartialSetStructure L V) (part : V → P) (S : Set V) :
    completeOutputPartGraph (wholeWeakInduce A S)
        (part ∘ Subtype.val) =
      (completeOutputPartGraph A part).induce S := by
  apply RelStructure.rel_injective
  funext R xs
  exact propext
    (wholeWeakInduce_completeOutputPartGraph_rel_iff A part S R xs)

/-- Whole-fibre weak function-closed subsets correspond to closed subsets
under the induced AMBIENT complete-part relations on the exact SAME S. -/
theorem wholeWeakInduce_isClosed_iff_inducedCompletePartGraph
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).IsClosed Q ↔
      IsClosedByCompleteParts
        ((completeOutputPartGraph A part).induce S) Q := by
  have h := isClosed_iff_completePartGraph_isClosed
    (wholeWeakInduce A S) (part ∘ Subtype.val)
    (FibreTransversal.wholeWeakInduce A part hTrans S) Q
  rw [wholeWeakInduce_completeOutputPartGraph_eq A part S] at h
  exact h

/-- Equality of the native vertex closure INSIDE the exact weak test S
with closure under the induced AMBIENT finite complete-value relations. -/
theorem wholeWeakInduce_functionClosure_eq_inducedCompletePartHull
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).functionClosure Q =
      completePartClosureHull
        ((completeOutputPartGraph A part).induce S) Q := by
  have h := completePartClosureHull_eq_functionClosure
    (wholeWeakInduce A S) (part ∘ Subtype.val)
    (FibreTransversal.wholeWeakInduce A part hTrans S) Q
  rw [wholeWeakInduce_completeOutputPartGraph_eq A part S] at h
  exact h.symm

/-- The intrinsic finite generator bound of an exact whole-fibre weak test
is the one computed by the induced ambient finite complete-value
relational presentation, not by the closure of S in the full A. -/
theorem wholeWeakInduce_generatedByAtMost_iff_inducedCompletePartGraph
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (n : ℕ) :
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
      CompletePartGeneratedByAtMost
        ((completeOutputPartGraph A part).induce S) n := by
  have h := generatedByAtMost_iff_completePartGraph
    (wholeWeakInduce A S) (part ∘ Subtype.val)
    (FibreTransversal.wholeWeakInduce A part hTrans S) n
  rw [wholeWeakInduce_completeOutputPartGraph_eq A part S] at h
  exact h

end StructuralRamsey.PartialSetStructure

import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Exact agreement of clipped and whole-fibre weak partial-function restrictions

The two genuine Option(Set)-valued weak restriction conventions are
different for arbitrary multivalued function outputs:

* weakInduce clips any partially surviving nonempty output to S;
* wholeWeakInduce makes a defined application undefined whenever
  even one of its output vertices leaves S.

The value-level agreement iff an entire output lies in S or is
disjoint from S was checked earlier. This file upgrades it to
the WHOLE partial-function STRUCTURE, on the SAME exact carrier S,
with the ordinary relations retained literally.

In particular the two conventions ALWAYS coincide for structures
whose defined function outputs contain at most one vertex (including
genuinely defined-empty and undefined inputs). This is the
standard partial single-valued special case frequently used in
the survey, but it does not justify identifying the conventions
for arbitrary transversal multivalued outputs.

Neither proof changes an arbitrary tested S to its generated
closure, alters a source domain, or assumes a false tree completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- On the exact weak carrier S, no defined function output may have
both one vertex inside S and another outside S. -/
def NoPartiallyRetainedValues
    (A : PartialSetStructure L V) (S : Set V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (U : Set V),
    A.func F (Subtype.val ∘ xs) = some U →
    U ⊆ S ∨ ¬ (U ∩ S).Nonempty

/-- Entire structures are literally equal under the two weak
conventions whenever there is no partly clipped value.
This includes defined-empty, repetitions and nullary symbols. -/
theorem weakInduce_eq_wholeWeakInduce_of_noPartial
    (A : PartialSetStructure L V) (S : Set V)
    (hNo : NoPartiallyRetainedValues A S) :
    A.weakInduce S = A.wholeWeakInduce S := by
  classical
  cases A with
  | mk rel fn =>
    change PartialSetStructure.mk
      (fun R xs => rel R (Subtype.val ∘ xs))
      (fun F xs => weakValue S (fn F (Subtype.val ∘ xs))) =
      PartialSetStructure.mk
      (fun R xs => rel R (Subtype.val ∘ xs))
      (fun F xs => wholeWeakValue S (fn F (Subtype.val ∘ xs)))
    congr 1
    funext F xs
    cases hv : fn F (Subtype.val ∘ xs) with
    | none =>
        rfl
    | some U =>
        change weakValue S (some U) = wholeWeakValue S (some U)
        exact (wholeWeakValue_eq_weakValue_of_all_or_none S U
          (hNo F xs U hv)).symm

/-- If EVERY defined output fibre is empty or a singleton, the
clipped and whole-fibre weak structures coincide on every S,
WITHOUT requiring S to be function-closed. -/
theorem weakInduce_eq_wholeWeakInduce_of_singletonValues
    (A : PartialSetStructure L V)
    (hSingle : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V) (U : Set V),
      A.func F xs = some U →
      ∀ y z : V, y ∈ U → z ∈ U → y = z)
    (S : Set V) :
    A.weakInduce S = A.wholeWeakInduce S := by
  apply weakInduce_eq_wholeWeakInduce_of_noPartial A S
  intro F xs U hValue
  by_cases hFull : U ⊆ S
  · exact Or.inl hFull
  · right
    rintro ⟨y, hyU, hyS⟩
    apply hFull
    intro z hzU
    have hEq : z = y :=
      hSingle F (Subtype.val ∘ xs) U hValue z y hzU hyU
    rw [hEq]
    exact hyS

end StructuralRamsey.PartialSetStructure

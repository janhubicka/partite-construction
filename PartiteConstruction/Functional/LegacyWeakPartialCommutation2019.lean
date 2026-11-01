import PartiteConstruction.Functional.LegacyClippedPartialWeakDictionary2019
import PartiteConstruction.Functional.PartialWeakClippingWholeSingletonDictionary2019

/-!
# Track A: the printed weak restriction commutes with its exact partial decoder

The legacy Structure encodes a defined application only when its output fibre
is nonempty. In that convention, the source-faithful conversion
toNonemptyPartial and the *clipped* vertex-exact weak restriction commute
as WHOLE Option(Set)-valued structures; no domain bit has to be collapsed.

In particular, we can invoke the exact no-partly-retained-fibre criterion
from PartialWeakClippingWholeSingletonDictionary2019 and recover the precise
condition under which whole-fibre deletion equals the printed weak structure.
This does NOT license substituting whole-fibre weak tests for clipped tests
when a multivalued fibre has outputs on both sides of the cut.

No generator hull, extra vertices, positivity of arities, or closure of S.
-/


namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- This is stronger than equality after collapseDomain: the original
nonempty-domain bit commutes with clipping on exactly the same weak carrier S.
Originally empty fibres remain undefined, and surviving outputs give exactly
one defined value, even for multivalued and nullary operations. -/
theorem toNonemptyPartial_weakInduce_commute
    (A : Structure L V) (S : Set V) :
    (A.weakInduce S).toNonemptyPartial =
      A.toNonemptyPartial.weakInduce S := by
  classical
  cases A with
  | mk rel fn =>
    change PartialSetStructure.mk
      (fun R xs => rel R (Subtype.val ∘ xs))
      (fun F xs =>
        if ({y : S | y.1 ∈ fn F (Subtype.val ∘ xs)} : Set S).Nonempty then
          some {y : S | y.1 ∈ fn F (Subtype.val ∘ xs)}
        else none) =
      PartialSetStructure.mk
        (fun R xs => rel R (Subtype.val ∘ xs))
        (fun F xs =>
          PartialSetStructure.weakValue S
            (if (fn F (Subtype.val ∘ xs)).Nonempty then
              some (fn F (Subtype.val ∘ xs)) else none))
    congr 1
    funext F xs
    let U : Set V := fn F (Subtype.val ∘ xs)
    change (if ({y : S | y.1 ∈ U} : Set S).Nonempty then
      some {y : S | y.1 ∈ U} else none) =
        PartialSetStructure.weakValue S
          (if U.Nonempty then some U else none)
    have hSurv :
        ({y : S | y.1 ∈ U} : Set S).Nonempty ↔
          (U ∩ S).Nonempty := by
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y.1, hy, y.2⟩
      · rintro ⟨y, hy, hS⟩
        exact ⟨⟨y, hS⟩, hy⟩
    by_cases hU : U.Nonempty
    · by_cases hMeet : (U ∩ S).Nonempty
      · have hLeft : ({y : S | y.1 ∈ U} : Set S).Nonempty :=
          hSurv.mpr hMeet
        simp [PartialSetStructure.weakValue, hU, hMeet, hLeft]
      · have hLeft : ¬ ({y : S | y.1 ∈ U} : Set S).Nonempty :=
          fun h => hMeet (hSurv.mp h)
        simp [PartialSetStructure.weakValue, hU, hMeet, hLeft]
    · have hLeft : ¬ ({y : S | y.1 ∈ U} : Set S).Nonempty := by
        rintro ⟨y, hy⟩
        exact hU ⟨y.1, hy⟩
      simp [PartialSetStructure.weakValue, hU, hLeft]

/-- A sharp native/partial dictionary: the native clipped weak structure
has precisely the same nonempty-defined partial operations as whole-value
deletion iff no defined output is partly retained by the exact cut. -/
theorem toNonemptyPartial_weakInduce_eq_whole_iff
    (A : Structure L V) (S : Set V) :
    (A.weakInduce S).toNonemptyPartial =
      A.toNonemptyPartial.wholeWeakInduce S ↔
    PartialSetStructure.NoPartiallyRetainedValues A.toNonemptyPartial S := by
  rw [toNonemptyPartial_weakInduce_commute]
  exact PartialSetStructure.weakInduce_eq_wholeWeakInduce_iff_noPartial
    A.toNonemptyPartial S

/-- The weaker collapsed old structure likewise agrees with whole-fibre
deletion whenever the exact no-partial-fibre condition holds. -/
theorem collapseDomain_wholeWeakInduce_of_noPartial
    (A : Structure L V) (S : Set V)
    (hNo : PartialSetStructure.NoPartiallyRetainedValues
      A.toNonemptyPartial S) :
    (A.toNonemptyPartial.wholeWeakInduce S).collapseDomain =
      A.weakInduce S := by
  have hEq :
      A.toNonemptyPartial.weakInduce S =
        A.toNonemptyPartial.wholeWeakInduce S :=
    PartialSetStructure.weakInduce_eq_wholeWeakInduce_of_noPartial
      A.toNonemptyPartial S hNo
  calc
    (A.toNonemptyPartial.wholeWeakInduce S).collapseDomain =
        (A.toNonemptyPartial.weakInduce S).collapseDomain :=
      congrArg (fun T : PartialSetStructure L S => T.collapseDomain) hEq.symm
    _ = A.weakInduce S :=
      collapseDomain_weakInduce_toNonemptyPartial A S

end StructuralRamsey.Structure

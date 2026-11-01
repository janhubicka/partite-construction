import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Structure.WeakSubstructure

/-!
# Exact original survey weak clipping as a genuine partial decoder

The printed total set-valued weak substructure clips each output
set to the literal vertex set S. The existing toNonemptyPartial
bridge interprets a nonempty legacy fibre as a DEFINED Option(Set)
value and an empty fibre as none. We check that the CLIPPED weak
partial restriction followed by collapsing the explicit domain
is EXACTLY the printed legacy weak restriction on the same S,
even for genuinely multivalued outputs partially crossing S.

This is not whole-fibre weak deletion: the latter differs when
some outputs survive and others leave. The independent
all-or-none/singleton dictionary determines its exact scope.
No closure hull and no extra vertices are used.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every legacy clipped weak fibre is recovered from the genuinely
partial CLIPPED weak value after forgetting the domain bit. -/
theorem collapseDomain_weakInduce_toNonemptyPartial_func
    (A : Structure L V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) :
    ((A.toNonemptyPartial.weakInduce S).collapseDomain).func F xs =
      (A.weakInduce S).func F xs := by
  classical
  let U : Set V := A.func F (Subtype.val ∘ xs)
  change
    (PartialSetStructure.weakValue S
      (if U.Nonempty then some U else none)).getD ∅ =
      {y : S | y.1 ∈ U}
  by_cases hNonempty : U.Nonempty
  · by_cases hMeet : (U ∩ S).Nonempty
    · simp [PartialSetStructure.weakValue, hNonempty, hMeet]
    · have hZero : ({y : S | y.1 ∈ U} : Set S) = ∅ := by
        ext y
        constructor
        · intro hy
          exact (hMeet ⟨y.1, hy, y.2⟩).elim
        · simp
      simp [PartialSetStructure.weakValue, hNonempty, hMeet, hZero]
  · have hZero : U = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hNonempty ⟨y, hy⟩).elim
      · simp
    simp [hZero, PartialSetStructure.weakValue]

/-- The WHOLE printed legacy weak structure is exactly the collapse
of the genuine partial CLIPPED weak structure on the same S. -/
theorem collapseDomain_weakInduce_toNonemptyPartial
    (A : Structure L V) (S : Set V) :
    (A.toNonemptyPartial.weakInduce S).collapseDomain =
      A.weakInduce S := by
  classical
  cases A with
  | mk rel fn =>
    change Structure.mk
      (fun R xs => rel R (Subtype.val ∘ xs))
      (fun F xs =>
        (PartialSetStructure.weakValue S
          (if (fn F (Subtype.val ∘ xs)).Nonempty then
            some (fn F (Subtype.val ∘ xs))
          else none)).getD ∅) =
      Structure.mk
        (fun R xs => rel R (Subtype.val ∘ xs))
        (fun F xs => {y : S | y.1 ∈ fn F (Subtype.val ∘ xs)})
    congr 1
    funext F xs
    exact collapseDomain_weakInduce_toNonemptyPartial_func
      (Structure.mk rel fn) S F xs

end StructuralRamsey.Structure

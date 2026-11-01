import PartiteConstruction.Functional.PartialWeakClippingWholeSingletonDictionary2019

/-!
# Track A: clipping and whole-value deletion agree on function-closed cuts

This is the positive counterpart of the part-saturated multivalued regression:
when S is genuinely function-closed, EVERY defined output at a tuple in S
remains wholly in S, so the two genuine Option(Set)-valued weak conventions
are literally equal as entire structures on exactly S. No singleton-valued
assumption is needed, and some(∅), nullary symbols, and repeated inputs are
included.

Part-saturation is weaker than actual function-closedness and does not
suffice, as witnessed by PartSaturatedWholeWeakCounterexample2019.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Closedness is a sufficient condition for exact equality of the two
weak restriction conventions, even for multivalued function outputs. -/
theorem weakInduce_eq_wholeWeakInduce_of_closed
    (A : PartialSetStructure L V) (S : Set V)
    (hS : A.IsClosed S) :
    A.weakInduce S = A.wholeWeakInduce S := by
  apply weakInduce_eq_wholeWeakInduce_of_noPartial A S
  intro F xs U hU
  left
  exact hS F (Subtype.val ∘ xs) (fun i => (xs i).2) U hU

end StructuralRamsey.PartialSetStructure

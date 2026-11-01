import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Track A adversarial regression: multivalued but transversal weak fibres

One nullary and one binary function have exactly the same two-valued
output {0,1} on every input tuple. The part projection is the identity
on Fin 2, hence both fibres are genuinely transversal (one output per
distinct part), even though they are NOT singleton-valued.

On S={0}, clipped weak restriction keeps the surviving value {0},
but whole-fibre weak restriction makes the application undefined. This
holds both at a nullary root and at a repeated-input binary root.

Separately verify that some(∅) remains defined under BOTH restrictions
and none remains undefined, for either function and every exact S.

The test prevents the false shortcut "transversal => singleton-valued"
and is independent of any Ramsey/tree-completion hypothesis.
-/

namespace StructuralRamsey.FunctionalPartite.TrackA

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

def mixedArityLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Bool
  relArity := Empty.elim
  funcArity
    | false => 0
    | true => 2

def mixedNative : Structure mixedArityLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := Set.univ

/-- This is a genuine functional partite system, not merely an arbitrary
two-valued function. Distinct outputs have distinct vertex parts. -/
def mixedPartite : System mixedArityLanguage (Fin 2) (Fin 2) :=
  transversal mixedNative

theorem mixedPartite_output_transversal
    (F : Bool) (xs : Fin (mixedArityLanguage.funcArity F) → Fin 2) :
    Set.InjOn mixedPartite.part (mixedPartite.func F xs) :=
  mixedPartite.func_part_injOn F xs

theorem mixedPartite_two_distinct_outputs :
    (0 : Fin 2) ∈ mixedPartite.func true (fun _ => 0) ∧
    (1 : Fin 2) ∈ mixedPartite.func true (fun _ => 0) := by
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

def mixedPartial : PartialSetStructure mixedArityLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := some Set.univ

def cut : Set (Fin 2) := {0}

def cutInput (F : Bool) : Fin (mixedArityLanguage.funcArity F) → cut :=
  fun _ => ⟨0, by simp [cut]⟩

private theorem cross_meets :
    ((Set.univ : Set (Fin 2)) ∩ cut).Nonempty :=
  ⟨0, Set.mem_univ _, by simp [cut]⟩

private theorem cross_escapes :
    ¬ (Set.univ : Set (Fin 2)) ⊆ cut := by
  intro h
  have h1 : (1 : Fin 2) ∈ cut := h (Set.mem_univ _)
  have hneq : (1 : Fin 2) ≠ 0 := by decide
  exact hneq (by simpa [cut] using h1)

/-- Witness for failure of the two exact partial weak operations.
This covers F=false (nullary), and F=true (binary with repeated 0). -/
theorem clipped_ne_whole_for_each_arity (F : Bool) :
    (mixedPartial.weakInduce cut).func F (cutInput F) ≠
      (mixedPartial.wholeWeakInduce cut).func F (cutInput F) := by
  change PartialSetStructure.weakValue cut (some (Set.univ : Set (Fin 2))) ≠
    PartialSetStructure.wholeWeakValue cut (some (Set.univ : Set (Fin 2)))
  exact (PartialSetStructure.wholeWeakValue_ne_weakValue_of_partial
    cut Set.univ cross_meets cross_escapes).symm

theorem clipped_ne_whole_nullary :
    (mixedPartial.weakInduce cut).func false (cutInput false) ≠
      (mixedPartial.wholeWeakInduce cut).func false (cutInput false) :=
  clipped_ne_whole_for_each_arity false

theorem clipped_ne_whole_repeated_binary :
    (mixedPartial.weakInduce cut).func true (cutInput true) ≠
      (mixedPartial.wholeWeakInduce cut).func true (cutInput true) :=
  clipped_ne_whole_for_each_arity true

def emptyPartial : PartialSetStructure mixedArityLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := some ∅

def undefinedPartial : PartialSetStructure mixedArityLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := none

/-- Defined-empty survives both weak conventions at arbitrary sets, including
the empty carrier for nullaries. -/
theorem defined_empty_survives
    (S : Set (Fin 2)) (F : Bool)
    (xs : Fin (mixedArityLanguage.funcArity F) → S) :
    (emptyPartial.weakInduce S).func F xs = some (∅ : Set S) ∧
    (emptyPartial.wholeWeakInduce S).func F xs = some (∅ : Set S) := by
  change PartialSetStructure.weakValue S (some (∅ : Set (Fin 2))) =
      some (∅ : Set S) ∧
    PartialSetStructure.wholeWeakValue S (some (∅ : Set (Fin 2))) =
      some (∅ : Set S)
  simp

/-- Undefined input remains undefined under either weak restriction. -/
theorem undefined_survives
    (S : Set (Fin 2)) (F : Bool)
    (xs : Fin (mixedArityLanguage.funcArity F) → S) :
    (undefinedPartial.weakInduce S).func F xs = none ∧
    (undefinedPartial.wholeWeakInduce S).func F xs = none := by
  change PartialSetStructure.weakValue S none = none ∧
    PartialSetStructure.wholeWeakValue S none = none
  exact ⟨rfl, rfl⟩

end StructuralRamsey.FunctionalPartite.TrackA

import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.PartialWeakClippingWholeSingletonDictionary2019

/-!
# Track A: part-saturation does not identify clipped and whole-fibre weak functions

A part-saturated set need not be function-closed. More significantly, even a
part-saturated test of a genuinely transversal functional partite system may
retain one output of a multivalued function while dropping another output in
a different part. Hence part-saturation plus output transversality does not
imply the no-partial-fibre hypothesis of the whole-fibre weak dictionary.

A binary function with a value consisting of the two distinct part vertices
is enough. The construction has a repeated-input tuple, no relations, and
an honest partite System; its genuine Option(Set) presentation has the
same whole underlying old set-valued structure.

This is a counterexample to the invalid transfer, NOT to the correct
part-saturated original-partial projection of the native Picture support.
-/

namespace StructuralRamsey.FunctionalPartite.TrackASaturation

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 2

def base : Structure language (Fin 2) where
  rel R := Empty.elim R
  func _ _ := Set.univ

def system : System language (Fin 2) (Fin 2) :=
  transversal base

def partial : PartialSetStructure language (Fin 2) where
  rel R := Empty.elim R
  func _ _ := some Set.univ

def S : Set (Fin 2) := {0}

/-- The partial model is a faithful defined-nonempty presentation of the
genuine transversal native System. No change in its function outputs. -/
theorem partial_collapse_eq_system :
    partial.collapseDomain = system.toStructure := rfl

theorem output_transversal :
    Set.InjOn system.part (system.func () (fun _ => (0 : Fin 2))) :=
  system.func_part_injOn () (fun _ => 0)

theorem two_outputs :
    (0 : Fin 2) ∈ system.func () (fun _ => 0) ∧
    (1 : Fin 2) ∈ system.func () (fun _ => 0) := by
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- The one-vertex cut S={0} is a whole union of its occupied parts:
the part map here is literally the identity on Fin 2. -/
theorem cut_partSaturated : system.PartSaturated S := by
  intro y hy
  rcases hy with ⟨x, hx, hxy⟩
  change x = y at hxy
  exact hxy ▸ hx

private theorem meets :
    ((Set.univ : Set (Fin 2)) ∩ S).Nonempty :=
  ⟨0, Set.mem_univ _, by simp [S]⟩

private theorem escapes :
    ¬ (Set.univ : Set (Fin 2)) ⊆ S := by
  intro h
  have h1 : (1 : Fin 2) ∈ S := h (Set.mem_univ _)
  have hne : (1 : Fin 2) ≠ 0 := by decide
  exact hne (by simpa [S] using h1)

/-- Even with every function-output fibre transversal and S
part-saturated, the clipped and whole-fibre genuine weak structures
differ on this exact S. -/
theorem partSaturated_not_enough :
    system.PartSaturated S ∧
      partial.weakInduce S ≠ partial.wholeWeakInduce S := by
  constructor
  · exact cut_partSaturated
  · intro heq
    have hNo := (weakInduce_eq_wholeWeakInduce_iff_noPartial
      partial S).mp heq
    let xs : Fin 2 → S := fun _ => ⟨0, by simp [S]⟩
    have hValue :
        partial.func () (Subtype.val ∘ xs) =
          some (Set.univ : Set (Fin 2)) := rfl
    rcases hNo () xs Set.univ hValue with hSub | hDisjoint
    · exact escapes hSub
    · exact hDisjoint meets

end StructuralRamsey.FunctionalPartite.TrackASaturation

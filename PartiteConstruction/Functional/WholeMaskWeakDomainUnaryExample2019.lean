import PartiteConstruction.Functional.WholeMaskWeakDomainObstruction2019

/-!
# Finite two-vertex unary regression for persistent mask-domain obstruction

With a single unary partial function F, put A={0,1},
F(0)=some {1} and F(1)=none. The exact weak subset S={0}
has F(0)=none, but its ambient induced OLD complete-mask graph
still has a positive domain tuple at 0.

Consequently the completely canonical OLD inclusion
(old(A).induce S) → old(A) is a full relational embedding,
while no full original partial-function embedding from
wholeWeakInduce A S → A agrees with that same inclusion.

This is a witnessed elementary counterexample to the naive
local *map transfer*, NOT to the global corrected 2019 theorem.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey

/-- One unary partial operation, no relations, on two vertices. -/
def weakDomainUnaryToy :
    PartialSetStructure exampleLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ xs =>
    if xs (0 : Fin 1) = (0 : Fin 2)
    then some ({(1 : Fin 2)} : Set (Fin 2))
    else none

/-- Naming each vertex as its own part is automatically transversal. -/
theorem weakDomainUnaryToy_transversal :
    FibreTransversal weakDomainUnaryToy (fun x : Fin 2 => x) := by
  intro F xs U hValue y hy z hz heq
  exact heq

/-- Concrete original operation at vertex 0 is defined with output 1. -/
theorem weakDomainUnaryToy_value :
    weakDomainUnaryToy.func ()
      (fun _ : Fin 1 => (0 : Fin 2)) =
      some ({(1 : Fin 2)} : Set (Fin 2)) := by
  rfl

/-- The original output 1 does not survive in S={0}. -/
theorem weakDomainUnaryToy_lost :
    ¬ ({(1 : Fin 2)} : Set (Fin 2)) ⊆
      ({(0 : Fin 2)} : Set (Fin 2)) := by
  intro h
  have h10 : (1 : Fin 2) ∈ ({(0 : Fin 2)} : Set (Fin 2)) :=
    h (by simp)
  simp at h10

/-- The literal same-vertex OLD inclusion cannot be upgraded to a
FULL functional embedding of the exact weak restriction: the target
function is defined and the source weak function is undefined. -/
theorem weakDomainUnaryToy_no_full_weak_inclusion :
    ¬ ∃ e : Embedding
      (wholeWeakInduce weakDomainUnaryToy
        ({(0 : Fin 2)} : Set (Fin 2)))
      weakDomainUnaryToy,
      ∀ x : ({(0 : Fin 2)} : Set (Fin 2)), e.toFun x = x.1 := by
  let S : Set (Fin 2) := {(0 : Fin 2)}
  let xs : Fin 1 → S := fun _ => ⟨0, by simp [S]⟩
  have hv : weakDomainUnaryToy.func ()
      (Subtype.val ∘ xs) =
      some ({(1 : Fin 2)} : Set (Fin 2)) := by
    exact weakDomainUnaryToy_value
  have hLost : ¬ ({(1 : Fin 2)} : Set (Fin 2)) ⊆ S :=
    weakDomainUnaryToy_lost
  exact canonicalOldInclusion_not_fullWeakEmbedding_of_lost_output
    weakDomainUnaryToy (fun x : Fin 2 => x)
    weakDomainUnaryToy_transversal
    S () xs {(1 : Fin 2)} hv hLost

end StructuralRamsey.PartialSetStructure

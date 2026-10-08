import PartiteConstruction.Functional.NativePowerTreeSquare
import PartiteConstruction.Functional.WeakInvariant

/-! # Disjoint functional pictures cannot have a globally full part projection

A simple issue in the functional reading of the published induced construction:
the initial picture is a disjoint union of full B-copies.  When B has a
binary function F(0,1)={2}, the projection of TWO disjoint copies back to B
preserves every existing function value but is NOT a full homomorphism.
The cross-copy input tuple has no function output in the source, while
its image in B has an output.

Thus the native EHN construction correctly records a WEAK projection
(full on irreducibles), whereas the published property (1) of
thm:sparseningRamsey requires a FULL homomorphism-embedding into C0.
This is not cured by treating the projected image weakly: that fixes
the size induction but cannot change global function-domain reflection.
-/

namespace StructuralRamsey.Structure.PublishedFunctionalProjectionObstruction

open StructuralRamsey.Structure
open StructuralRamsey.Structure.NativePowerObstruction

/-- Two disjoint full copies of the 3-vertex binary-function template. -/
def doubleCopy : Structure toyLanguage (Bool × Fin 3) where
  rel R x := (x (0 : Fin 1)).2 = R
  func _ x := {z |
    (x (0 : Fin 2)).1 = (x (1 : Fin 2)).1 ∧
    z.1 = (x (0 : Fin 2)).1 ∧
    z.2 ∈ toyBase.func ()
      (fun i : Fin 2 => (x i).2)}

/-- The natural map back to the template is weak: every source function
value is mapped to a target value. -/
theorem projection_weak :
    doubleCopy.IsWeakHomomorphism toyBase Prod.snd := by
  constructor
  · intro R x hx
    exact hx
  · intro F x z hz
    exact hz.2.2

def mixedInput : Fin 2 → Bool × Fin 3 :=
  ![(false, 0), (true, 1)]

theorem mixedInput_empty :
    ¬ (doubleCopy.func () mixedInput).Nonempty := by
  rintro ⟨z, hz⟩
  have heq : (false : Bool) = true := hz.1
  exact Bool.noConfusion heq

theorem mixedInput_target_defined :
    (toyBase.func () (Prod.snd ∘ mixedInput)).Nonempty := by
  refine ⟨(2 : Fin 3), ?_⟩
  change (Prod.snd ∘ mixedInput) (0 : Fin 2) = 0 ∧
    (Prod.snd ∘ mixedInput) (1 : Fin 2) = 1 ∧
    (2 : Fin 3) = 2
  decide

/-- The part projection from the initial two-copy picture is not a full
function homomorphism. This disproves an automatic upgrade of the native
weak projection in the original appendix proof. -/
theorem projection_not_full :
    ¬ doubleCopy.IsHomomorphism toyBase Prod.snd := by
  intro hp
  obtain ⟨z, hz⟩ := mixedInput_target_defined
  have himage :
      z ∈ imageSet Prod.snd (doubleCopy.func () mixedInput) := by
    rw [hp.2 () mixedInput]
    exact hz
  rcases himage with ⟨w, hw, _⟩
  exact mixedInput_empty ⟨w, hw⟩

end StructuralRamsey.Structure.PublishedFunctionalProjectionObstruction

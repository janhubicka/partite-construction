import PartiteConstruction.Functional.MaximalHardRootFiveCycleFixture
import PartiteConstruction.Functional.Induced

/-!
# Track D: the arbitrary-stage C5 core is NOT a genuine selected HJ power

The actual functional Hales--Jewett Picture starts with a selected
support over precisely the two part labels alpha(A)={0,3} and forms
a genuine tagged partite power, subsequently relabelled along alpha.

Every tagged power vertex still has one of the original selected part
labels. In particular, there cannot be a part-respecting map from
the arbitrary C5 counterexample CORE into such a power: the core's
interior vertex d1 has part 1. This proves in Lean the precise
history/part-range defect that prevents the existing C5 fixture from
refuting a history-restricted HJ Picture theorem.

The source fixture DOES refute unrestricted arbitrary-stage binary
attachment strict-tree preservation. This file does not prove that
the actual HJ Picture always has strict B-tree completions; the genuine
three-line C7 regression and maximal mixed root remain open.
-/

namespace StructuralRamsey.Structure.MaximalHardRootFiveCycle

open StructuralRamsey.FunctionalPartite

/-- The selected old A support uses labels 0 and 3. -/
def selectedPart (x : Fin 2) : Fin 5 :=
  if x = 0 then 0 else 3

theorem selectedPart_ne_one (x : Fin 2) :
    selectedPart x ≠ (1 : Fin 5) := by
  fin_cases x <;> decide

/-- No part-respecting map from the FALSE C5 core to any actual tagged
HJ power of a system whose selected part alphabet is Fin 2 relabelled
by 0↦0, 1↦3. In particular, no part-preserving embedding exists.

This is a precise impossibility about the HJ PART labels, not a claim
about all multi-line Picture histories. -/
theorem c5_core_not_selected_HJ_power
    {W : Type} (R : System language (Fin 2) W) (N : ℕ)
    (map : Fin 5 → Induced.Vertex R N)
    (hPart : ∀ x : Fin 5,
      selectedPart ((Induced.power R N).part (map x)) = corePart x) :
    False := by
  have h := hPart (1 : Fin 5)
  have hc : corePart (1 : Fin 5) = (1 : Fin 5) := by decide
  rw [hc] at h
  exact selectedPart_ne_one _ h

end StructuralRamsey.Structure.MaximalHardRootFiveCycle

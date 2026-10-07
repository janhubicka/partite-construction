import PartiteConstruction.Functional.RelativeHistoryRootedWithHistory

/-! # Recovering an outer projection from finite singleton histories

The common completed separator in the functional iteration may identify
distinct source vertices.  The weak EHN projection must nevertheless factor
through those identifications.  Requesting all singleton sets of the finite
outer carrier as projected history forces precisely this kernel condition.

Given a nonempty outer carrier, a function on the image of the quotient
extends to its whole target by an arbitrary choice outside that image.
This isolates an elementary but essential compatibility condition for
the reducible-root induction.
-/

namespace StructuralRamsey.Structure

universe v

variable {H G P : Type v}

/-- The finite history which records every singleton in a finite outer
projection carrier.  It may be reused at each recursive Picture step. -/
noncomputable def singletonProjectedHistory (P : Type v) [Fintype P] :
    List (Set P) :=
  (Finset.univ : Finset P).toList.map Set.singleton

theorem singleton_mem_singletonProjectedHistory
    [Fintype P] (a : P) :
    Set.singleton a ∈ singletonProjectedHistory P := by
  unfold singletonProjectedHistory
  apply List.mem_map.mpr
  exact ⟨a, by simp, rfl⟩


/-- Preserving every singleton projected-history set implies that any two
source vertices identified in the target have equal outer projections. -/
theorem projectedKernel_of_singletonHistory
    (p : H → P) (q : H → G)
    (history : List (Set P))
    (hSingle : ∀ a : P, Set.singleton a ∈ history)
    (hHist :
      ∀ K ∈ history, ∀ x y : H,
        q x = q y → (p x ∈ K ↔ p y ∈ K)) :
    ∀ x y, q x = q y → p x = p y := by
  intro x y hxy
  have hmem : p y ∈ Set.singleton (p x) :=
    (hHist (Set.singleton (p x)) (hSingle (p x)) x y hxy).mp
      (by simp)
  have hEq : p y = p x := by
    simpa using hmem
  exact hEq.symm

/-- A map which is constant on the fibres of a quotient map factors through
that quotient.  The target projection need not be a homomorphism; only
its values on the image of the distinguished root are constrained. -/
theorem projectedMap_factors_of_kernel
    [Nonempty P]
    (p : H → P) (q : H → G)
    (hKer : ∀ x y, q x = q y → p x = p y) :
    ∃ pG : G → P, ∀ x, p x = pG (q x) := by
  classical
  let pG (g : G) : P :=
    if hg : ∃ x : H, q x = g then p (Classical.choose hg)
    else Classical.choice inferInstance
  refine ⟨pG, ?_⟩
  intro x
  have hx : ∃ z : H, q z = q x := ⟨x, rfl⟩
  have hval : pG (q x) = p (Classical.choose hx) := by
    simp only [pG, dif_pos hx]
  rw [hval]
  exact hKer x (Classical.choose hx)
    (Classical.choose_spec hx).symm

/-- Projected-history preservation of all singleton sets supplies the factor
map required by strict common-root gluing, without assuming injectivity of
the chosen completion of the separator. -/
theorem projectedMap_factors_of_singletonHistory
    [Nonempty P]
    (p : H → P) (q : H → G)
    (history : List (Set P))
    (hSingle : ∀ a : P, Set.singleton a ∈ history)
    (hHist :
      ∀ K ∈ history, ∀ x y : H,
        q x = q y → (p x ∈ K ↔ p y ∈ K)) :
    ∃ pG : G → P, ∀ x, p x = pG (q x) := by
  exact projectedMap_factors_of_kernel p q
    (projectedKernel_of_singletonHistory p q history hSingle hHist)

end StructuralRamsey.Structure

import PartiteConstruction.Functional.OccupiedAlphaPredecessor
import PartiteConstruction.Functional.WeakWitnessRestriction

/-!
# Budgeted genuine FULL alpha collars from the ORDINARY predecessor

The false unrestricted fixed A-collar invariant is NOT assumed here.
Let I be the exact weak projected test in the previous control D,
and alpha:A↪D its actual full selected A-placement.

When the explicitly finite auxiliary set
  J = I ∪ alpha[A]
has cardinality ≤m, the verified ordinary rank-m strict
full-functional weak-history invariant on D can be asked about J.
The ambient-A intersection property and singleton histories give an
exact protected FULL alpha mark on J (OccupiedAlphaPredecessor).
The same complete strict B-tree target and marked A-copy restrict
back to EXACT I using WeakWitnessRestriction.

This creates no generated closure of I, changes no source weak test,
and does not assume global total-fibre homomorphisms or singleton
function values. The extra alpha vertices are charged explicitly
within the EXISTING predecessor cardinal budget m; if that budget
fails, this lemma makes no assertion.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost

universe u v
variable {L : Language.{u}} {UA VB P : Type v}

/-- A strict FULL-functional predecessor weak-tree witness on an
auxiliary J=I∪alpha(A) yields an exact fully protected target A
mark on the original weak I whenever |J|≤m.

This is the precise positive portion of the published functional
mixed-root induction not covered by the parity counterexample. -/
theorem protected_of_union_budget
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} [Fintype P] [Fintype UA] [DecidableEq P]
    {m : ℕ}
    (hPrev : AtMost A Base D (id : P → P) m)
    (I : Finset P)
    (alpha : Embedding A D)
    (hBudget :
      (I ∪ (Finset.univ : Finset UA).image alpha).card ≤ m)
    (history : List (Set P)) :
    SetAmbientProtectedWeakTreeWitness A Base alpha D
      (id : P → P) (↑I : Set P) history := by
  classical
  let J : Finset P :=
    I ∪ (Finset.univ : Finset UA).image alpha
  have hJCard : J.card ≤ m := hBudget
  have hAll : ∀ a : UA, alpha a ∈ J := by
    intro a
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist,
    mark, hContained, hTrace⟩ :=
    hPrev.fullAlpha_witness J hJCard alpha hAll history
  have hProtected : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P) (↑J : Set P) history := by
    exact ⟨Z, Target, hTree, f, hWeak, hCopies,
      hHist, mark, hContained, hTrace⟩
  have hSub : (↑I : Set P) ⊆ (↑J : Set P) := by
    intro x hx
    exact Finset.mem_union_left _ hx
  exact hProtected.restrict_subset (↑I : Set P) hSub

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost

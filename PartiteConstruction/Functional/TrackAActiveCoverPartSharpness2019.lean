import PartiteConstruction.Functional.TrackAActivePartCoverUnionFailure2019

/-!
# Track A adversarial regression — positive outputs are not enough
# without preservation of part labels

The new weak-map active-cover pullback theorem assumes both positive
function-incidence preservation and part-label preservation. The
second hypothesis is indispensable, even if the vertex map is a FULL
functional embedding of the underlying unpartited structures.

Use the existing genuine transversal three-vertex source System:
the one unary output set is {0,1}, with source part labels
part(0)=0, part(1)=part(2)=1. The weak subset S={0,2}
fails active-output-part cover: output 0 survives, while the
unique source output 1 has a part occupied by vertex 2 but is missing.

Keep exactly the SAME native functional structure and vertex set,
and change ONLY the part label of vertex 2 to 0. The new target
system is still output-transversal, as all function outputs lie at
vertices 0 and 1 where the labels are unchanged. Its same cut
S={0,2} is active-covered because S occupies only target part 0.
The identity map between the underlying native functional structures
is FULL and in particular positive, but fails to preserve part
labels. Its inverse-image weak cut fails source active cover.

This explicitly excludes dropping the part-preservation hypothesis
from the stronger Track A weak-map theorem. It is not an EHN-stage
counterexample or a strict mixed-root target-tree obstruction.
-/

namespace StructuralRamsey.FunctionalPartite.TrackAActiveCoverPartSharpness

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample
open StructuralRamsey.FunctionalPartite.TrackAActivePartCoverUnionFailure

/-- Reassign only the part of vertex 2, which is not an output of
any source function. At vertices 0,1 the old and new part labels
coincide, preserving transversality of the two-output fibre. -/
def alternatePart (x : Fin 3) : Fin 2 :=
  if x = (1 : Fin 3) then 1 else 0

def target : System exampleLanguage (Fin 2) (Fin 3) where
  toStructure := system.toStructure
  part := alternatePart
  relTransversal := by
    intro R
    exact Empty.elim R
  funcTransversal := by
    intro F xs y z hy hz hp
    have hyU : y ∈ output := by
      change y ∈ output at hy
      exact hy
    have hzU : z ∈ output := by
      change z ∈ output at hz
      exact hz
    have hyCases : y = (0 : Fin 3) ∨ y = 1 := by
      simpa [output] using hyU
    have hzCases : z = (0 : Fin 3) ∨ z = 1 := by
      simpa [output] using hzU
    have hY : alternatePart y = projection y := by
      rcases hyCases with h0 | h1
      · subst y
        simp [alternatePart, projection]
      · subst y
        simp [alternatePart, projection]
    have hZ : alternatePart z = projection z := by
      rcases hzCases with h0 | h1
      · subst z
        simp [alternatePart, projection]
      · subst z
        simp [alternatePart, projection]
    exact system.funcTransversal F xs y z hy hz
      (hY.symm.trans (hp.trans hZ))

def cut : Set (Fin 3) := left ∪ right

/-- Target support {0,2} has only part 0, so it is active-covered.
The target function value {0,1} still has two distinct output parts.
Thus this is a NONVACUOUS active fibre example. -/
theorem target_active :
    target.ActiveWeakOutputPartCover cut := by
  intro F xs hMeet y hy hPart
  have hyU : y ∈ output := by
    change y ∈ output at hy
    exact hy
  have hyCases : y = (0 : Fin 3) ∨ y = 1 := by
    simpa [output] using hyU
  rcases hyCases with h0 | h1
  · subst y
    exact Or.inl (by simp [left])
  · obtain ⟨z, hzCut, heq⟩ := hPart
    have hzCases : z = (0 : Fin 3) ∨ z = 2 := by
      rcases hzCut with hzL | hzR
      · exact Or.inl (by simpa [left] using hzL)
      · exact Or.inr (by simpa [right] using hzR)
    have hzPart : target.part z = (0 : Fin 2) := by
      rcases hzCases with hz0 | hz2
      · subst z
        rfl
      · subst z
        rfl
    have hyPart : target.part y = (1 : Fin 2) := by
      rw [h1]
      rfl
    have hBad : (1 : Fin 2) = 0 :=
      hyPart.symm.trans (heq.symm.trans hzPart)
    exact ((show (1 : Fin 2) ≠ 0 by decide) hBad).elim

/-- The identity is even a FULL unpartited functional embedding,
so positive output preservation is completely unproblematic here. -/
theorem underlying_full :
    ∃ e : Structure.Embedding system.toStructure target.toStructure,
      e.toFun = (id : Fin 3 → Fin 3) := by
  exact ⟨Structure.Embedding.id system.toStructure, rfl⟩

/-- Nonetheless the identity fails to preserve the part label at 2. -/
theorem identity_not_part_preserving :
    ¬ (∀ x : Fin 3, target.part ((id : Fin 3 → Fin 3) x) =
      system.part x) := by
  intro h
  have h2 := h (2 : Fin 3)
  have hBad : (0 : Fin 2) = 1 := by
    change alternatePart (2 : Fin 3) = projection 2 at h2
    simpa [alternatePart, projection] using h2
  exact ((show (0 : Fin 2) ≠ 1 by decide) hBad).elim

/-- Counterexample to a FALSE part-free strengthening: the full
unpartited identity maps into an active-covered target weak cut,
but its exact source preimage is not active-covered. -/
theorem active_cover_not_preimage_without_part_preservation :
    (∃ e : Structure.Embedding system.toStructure target.toStructure,
      e.toFun = (id : Fin 3 → Fin 3)) ∧
    target.ActiveWeakOutputPartCover cut ∧
    ¬ system.ActiveWeakOutputPartCover
      ((id : Fin 3 → Fin 3) ⁻¹' cut) := by
  refine ⟨underlying_full, target_active, ?_⟩
  change ¬ system.ActiveWeakOutputPartCover (left ∪ right)
  exact union_not_active

end StructuralRamsey.FunctionalPartite.TrackAActiveCoverPartSharpness

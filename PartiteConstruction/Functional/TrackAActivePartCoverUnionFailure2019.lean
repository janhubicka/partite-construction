import PartiteConstruction.Functional.TrackANativeActiveWeakOutputPartCover2019
import PartiteConstruction.Functional.PartialClippedWeakImageSaturationCounterexample2019

/-!
# Track A adversarial regression: active-cover weak supports need NOT
# remain active-cover under unions

The local `ActiveWeakOutputPartCover` criterion is stable under
intersections and full copy inverse images, as studied separately in
Track A. It is NOT stable under arbitrary unions, even for a genuine
native functionally transversal partite System.

Reuse the three-to-two vertex part map from the verified multivalued
projection obstruction:
    part(0)=0, part(1)=part(2)=1;
a single unary operation has output set {0,1} (defined at all inputs).
The output set is transversal to the part map.

The one-vertex supports {0} and {2} each satisfy active cover.
In their union {0,2}, the unary value has a surviving output 0 and
the occupied part label 1, but the unique genuine output vertex 1
was omitted. Therefore active cover fails. This is the obstruction
to treating local cover as automatically preserved by gluing arbitrary
weak supports along a common root.

This source-level finite regression does NOT assert that the finite
system occurs as an actual EHN stage, nor refute a history-restricted
mixed-root extension theorem or the ambient OLD U-closed route.
-/

namespace StructuralRamsey.FunctionalPartite.TrackAActivePartCoverUnionFailure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample

/-- The native partial source with the same independent output set,
equipped with its original three-to-two part map. -/
def system : System exampleLanguage (Fin 2) (Fin 3) where
  toStructure := source.collapseDomain
  part := projection
  relTransversal := by
    intro R
    exact Empty.elim R
  funcTransversal := by
    intro F xs y z hy hz hPart
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
    rcases hyCases with h0 | h1
    · rcases hzCases with h0' | h1'
      · exact h0.trans h0'.symm
      · have hBad : (0 : Fin 2) = 1 := by
          simpa [system, projection, h0, h1'] using hPart
        exact ((show (0 : Fin 2) ≠ 1 by decide) hBad).elim
    · rcases hzCases with h0' | h1'
      · have hBad : (1 : Fin 2) = 0 := by
          simpa [system, projection, h1, h0'] using hPart
        exact ((show (1 : Fin 2) ≠ 0 by decide) hBad).elim
      · exact h1.trans h1'.symm

/-- The two independent source cuts. -/
def left : Set (Fin 3) := {(0 : Fin 3)}
def right : Set (Fin 3) := {(2 : Fin 3)}

/-- A weak support occupying only part 0 has no missing active
output in an occupied part, even though output 1 is absent. -/
theorem left_active :
    system.ActiveWeakOutputPartCover left := by
  intro F xs hMeet y hy hPart
  obtain ⟨a, haLeft, haPart⟩ := hPart
  have hA : a = (0 : Fin 3) := by
    simpa [left] using haLeft
  have hyU : y ∈ output := by
    change y ∈ output at hy
    exact hy
  have hyCases : y = (0 : Fin 3) ∨ y = 1 := by
    simpa [output] using hyU
  rcases hyCases with hY0 | hY1
  · simpa [left] using hY0
  · have hBad : (0 : Fin 2) = 1 := by
      simpa [system, projection, hA, hY1] using haPart
    exact ((show (0 : Fin 2) ≠ 1 by decide) hBad).elim

/-- On the one-vertex cut {2}, the complete function output
{0,1} does not meet the cut at all, so the active-cover
condition is vacuous. -/
theorem right_active :
    system.ActiveWeakOutputPartCover right := by
  intro F xs hMeet y hy hPart
  obtain ⟨a, haOutput, haRight⟩ := hMeet
  have hA : a = (2 : Fin 3) := by
    simpa [right] using haRight
  have hOut : a ∈ output := by
    change a ∈ output at haOutput
    exact haOutput
  rw [hA] at hOut
  simp [output] at hOut

/-- The union has both part labels occupied, but the unique output
in part 1 is absent. Thus it fails active output-part cover. -/
theorem union_not_active :
    ¬ system.ActiveWeakOutputPartCover (left ∪ right) := by
  intro h
  let T : Set (Fin 3) := left ∪ right
  let xs : Fin 1 → T :=
    fun _ => ⟨0, Or.inl (by simp [left])⟩
  have hMeet :
      ((system.toStructure.func () (Subtype.val ∘ xs)) ∩ T).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · change (0 : Fin 3) ∈ output
      simp [output]
    · exact Or.inl (by simp [left])
  have hOutput :
      (1 : Fin 3) ∈ system.toStructure.func () (Subtype.val ∘ xs) := by
    change (1 : Fin 3) ∈ output
    simp [output]
  have hPart : system.part (1 : Fin 3) ∈ system.part '' T := by
    refine ⟨2, Or.inr (by simp [right]), ?_⟩
    simp [system, projection]
  have h1 : (1 : Fin 3) ∈ T :=
    h () xs hMeet 1 hOutput hPart
  have hNot : (1 : Fin 3) ∉ T := by
    simp [T, left, right]
  exact hNot h1

/-- Concrete failure of union stability among genuinely transversal
native functional partite supports. -/
theorem active_cover_not_union_closed :
    system.ActiveWeakOutputPartCover left ∧
    system.ActiveWeakOutputPartCover right ∧
    ¬ system.ActiveWeakOutputPartCover (left ∪ right) :=
  ⟨left_active, right_active, union_not_active⟩

end StructuralRamsey.FunctionalPartite.TrackAActivePartCoverUnionFailure

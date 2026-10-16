import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam

/-!
# Actual ambient A-copy intersections glue along exact weak free amalgams

The strict functional weak-tree invariant protects intersections of the
exact tested vertex set with ACTUAL full ambient A-copies. This is
weaker and more faithful to the published sparsening argument than
protecting every arbitrary closed partial-A embedding.

An irreducible full A-copy inside a full functional free amalgam is
wholly contained in one of the two sides. If the common target map
agrees with the two side maps on their exact weak subsets, then
the full target A-copy supplied by that side's history witness also
supplies the required completed A-copy for the whole weak test.

This theorem is independent of the target being a tree and independent
of the remaining existence of compatible weak common-root extensions.
No weak set is enlarged to its function closure, and no arbitrary
weak or partial-A copy is incorrectly assumed to be full.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {VA H E F C Y : Type v}

/-- Compatibility of the actual A-copy intersection certificates
with a FULL functional source free amalgam, for an arbitrary exact
weak vertex subset.

Only A.Irreducible is required to localize each full ambient
A-copy to one side; no hereditary irreducibility or closure of the
tested weak subset is assumed. -/
theorem ambientACopyIntersections_glue
    {A : Structure L VA}
    (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C) (Target : Structure L Y)
    (f : S → Y)
    (fL : (iL ⁻¹' S) → Y) (fR : (iR ⁻¹' S) → Y)
    (hfL : ∀ a : iL ⁻¹' S, f ⟨iL a.1, a.2⟩ = fL a)
    (hfR : ∀ b : iR ⁻¹' S, f ⟨iR b.1, b.2⟩ = fR b)
    (hL : SetAmbientACopyIntersections A Left Target
      (iL ⁻¹' S) fL)
    (hR : SetAmbientACopyIntersections A Right Target
      (iR ⁻¹' S) fR) :
    SetAmbientACopyIntersections A Whole Target S f := by
  intro e
  rcases hA hSrc e with hOnL | hOnR
  · choose lift hLift using hOnL
    let eL : Embedding A Left :=
      e.factorWithMap iL lift hLift
    obtain ⟨eT, hContained, hAgree⟩ := hL eL
    refine ⟨eT, hContained, ?_⟩
    intro a ha
    have haL : eL a ∈ iL ⁻¹' S := by
      change iL (lift a) ∈ S
      rw [← hLift a]
      exact ha
    have heq : (⟨e a, ha⟩ : S) =
        (⟨iL (eL a), haL⟩ : S) := by
      apply Subtype.ext
      exact hLift a
    calc
      eT a = fL ⟨eL a, haL⟩ := hAgree a haL
      _ = f ⟨iL (eL a), haL⟩ :=
        (hfL ⟨eL a, haL⟩).symm
      _ = f ⟨e a, ha⟩ := by
        rw [heq]
  · choose lift hLift using hOnR
    let eR : Embedding A Right :=
      e.factorWithMap iR lift hLift
    obtain ⟨eT, hContained, hAgree⟩ := hR eR
    refine ⟨eT, hContained, ?_⟩
    intro a ha
    have haR : eR a ∈ iR ⁻¹' S := by
      change iR (lift a) ∈ S
      rw [← hLift a]
      exact ha
    have heq : (⟨e a, ha⟩ : S) =
        (⟨iR (eR a), haR⟩ : S) := by
      apply Subtype.ext
      exact hLift a
    calc
      eT a = fR ⟨eR a, haR⟩ := hAgree a haR
      _ = f ⟨iR (eR a), haR⟩ :=
        (hfR ⟨eR a, haR⟩).symm
      _ = f ⟨e a, ha⟩ := by
        rw [heq]

end StructuralRamsey.Structure.IsFreeAmalgam

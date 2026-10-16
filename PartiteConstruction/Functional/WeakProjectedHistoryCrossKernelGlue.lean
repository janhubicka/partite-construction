import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam

/-!
# Exact weak projected-history diaries across genuine functional free amalgams

The published native functional Hales–Jewett Picture needs finite
projected history predicates to survive mixed weak-test completion,
not just positive function incidences and ambient full irreducibles.

This lemma identifies the EXACT missing cross-side condition. If a
whole weak-test target map extends side maps that each preserve their
projected histories, then the whole map preserves those histories
provided target equality between one left vertex and one right vertex
implies equality of their projected labels.

In a strict B-tree merge this cross-kernel condition is expected from
target free-amalgam overlap together with source-root ISOLATION and
a common projection factor through the completed root. Independent
tree witnesses do NOT automatically satisfy it.

The theorem remains in the genuine function language and on the
exact weak vertex set S. It assumes no closedness, singleton-valued
functions, or artificial global injectivity of the part projection.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C P Y : Type v}

/-- Compatibility of finite projected histories across an exact WEAK
test of a genuine full functional free amalgam reduces to the
CROSS-SIDE KERNEL condition. Side equalities use only the side
history properties; cross-side equalities require agreement of
projected labels and cannot be inferred from transversality alone.

This is source-faithful: the histories concern the actual ambient
part projection, not an invented completion of a weak root. -/
theorem setRespectsProjectedHistory_glue_crossKernel
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpL : ∀ a, pWhole (iL a) = pL a)
    (hpR : ∀ b, pWhole (iR b) = pR b)
    (f : S → Y)
    (fL : (iL ⁻¹' S) → Y) (fR : (iR ⁻¹' S) → Y)
    (hfL : ∀ a : iL ⁻¹' S, f ⟨iL a.1, a.2⟩ = fL a)
    (hfR : ∀ b : iR ⁻¹' S, f ⟨iR b.1, b.2⟩ = fR b)
    (history : List (Set P))
    (hHistL : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) fL history)
    (hHistR : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR history)
    (hCross : ∀ (a : iL ⁻¹' S) (b : iR ⁻¹' S),
      fL a = fR b → pL a.1 = pR b.1) :
    SetRespectsProjectedHistory pWhole S f history := by
  have hCoverS (z : S) :
      (∃ a : iL ⁻¹' S, z = (⟨iL a.1, a.2⟩ : S)) ∨
      (∃ b : iR ⁻¹' S, z = (⟨iR b.1, b.2⟩ : S)) := by
    rcases hSrc.covers z.1 with ⟨a, ha⟩ | ⟨b, hb⟩
    · have haS : iL a ∈ S := by
        rw [← ha]
        exact z.2
      exact Or.inl ⟨⟨a, haS⟩, by
        apply Subtype.ext
        exact ha⟩
    · have hbS : iR b ∈ S := by
        rw [← hb]
        exact z.2
      exact Or.inr ⟨⟨b, hbS⟩, by
        apply Subtype.ext
        exact hb⟩
  intro K hK x y hxy
  rcases hCoverS x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases hCoverS y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have hab : fL a = fL b := by
        calc
          fL a = f ⟨iL a.1, a.2⟩ := (hfL a).symm
          _ = f ⟨iL b.1, b.2⟩ := hxy
          _ = fL b := hfL b
      change pWhole (iL a.1) ∈ K ↔
        pWhole (iL b.1) ∈ K
      rw [hpL a.1, hpL b.1]
      exact hHistL K hK a b hab
    · have hab : fL a = fR b := by
        calc
          fL a = f ⟨iL a.1, a.2⟩ := (hfL a).symm
          _ = f ⟨iR b.1, b.2⟩ := hxy
          _ = fR b := hfR b
      change pWhole (iL a.1) ∈ K ↔
        pWhole (iR b.1) ∈ K
      rw [hpL a.1, hpR b.1, hCross a b hab]
  · rcases hCoverS y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have hab : fR a = fL b := by
        calc
          fR a = f ⟨iR a.1, a.2⟩ := (hfR a).symm
          _ = f ⟨iL b.1, b.2⟩ := hxy
          _ = fL b := hfL b
      change pWhole (iR a.1) ∈ K ↔
        pWhole (iL b.1) ∈ K
      rw [hpR a.1, hpL b.1, (hCross b a hab.symm).symm]
    · have hab : fR a = fR b := by
        calc
          fR a = f ⟨iR a.1, a.2⟩ := (hfR a).symm
          _ = f ⟨iR b.1, b.2⟩ := hxy
          _ = fR b := hfR b
      change pWhole (iR a.1) ∈ K ↔
        pWhole (iR b.1) ∈ K
      rw [hpR a.1, hpR b.1]
      exact hHistR K hK a b hab

end StructuralRamsey.Structure.IsFreeAmalgam

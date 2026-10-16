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


variable {G WL WR Z : Type v}

/-- In a genuine FULL functional TARGET free amalgam, a cross-side
equality of witness values must factor through its common full root.
If both side maps carry a prescribed projected label on every point
mapping into that target root, then such an equality necessarily
identifies points of the SAME projected source part.

This root-label factoring requirement is weaker than demanding
global injectivity or a full closed root embedding; it must still
be constructed in the maximal mixed functional Picture step. -/
theorem crossKernel_of_targetRootProjection
    {Start : Structure L G}
    {TargetL : Structure L WL} {TargetR : Structure L WR}
    {Target : Structure L Z}
    {sTL : Embedding Start TargetL}
    {sTR : Embedding Start TargetR}
    {jTL : Embedding TargetL Target}
    {jTR : Embedding TargetR Target}
    (hTgt : IsFreeAmalgam sTL sTR jTL jTR)
    {XLeft XRight : Type v}
    (fL : XLeft → WL) (fR : XRight → WR)
    (pL : XLeft → P) (pR : XRight → P)
    (pG : G → P)
    (hRootL : ∀ a g, fL a = sTL g → pL a = pG g)
    (hRootR : ∀ b g, fR b = sTR g → pR b = pG g)
    (a : XLeft) (b : XRight)
    (hab : jTL (fL a) = jTR (fR b)) :
    pL a = pR b := by
  obtain ⟨g, hLeft, hRight⟩ :=
    (hTgt.overlap (fL a) (fR b)).mp hab
  exact (hRootL a g hLeft).trans (hRootR b g hRight).symm

/-- Global projected-history preservation when the strict target is
built by FREE merging two full-functional target extensions over
one Start and their maps factor their projected labels through the
common target root.

The root-label-factor assumptions are explicit and NOT inferred from
unrelated predecessor tree completions. This is the exact target
history preservation needed after choosing coherent strict relative
side witnesses; no closure hull is used on the source weak test. -/
theorem setRespectsProjectedHistory_glue_targetRoot
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
    {Start : Structure L G}
    {TargetL : Structure L WL} {TargetR : Structure L WR}
    {Target : Structure L Z}
    {sTL : Embedding Start TargetL}
    {sTR : Embedding Start TargetR}
    {jTL : Embedding TargetL Target}
    {jTR : Embedding TargetR Target}
    (hTgt : IsFreeAmalgam sTL sTR jTL jTR)
    (f : S → Z)
    (fL : (iL ⁻¹' S) → WL)
    (fR : (iR ⁻¹' S) → WR)
    (hfL : ∀ a : iL ⁻¹' S,
      f ⟨iL a.1, a.2⟩ = jTL (fL a))
    (hfR : ∀ b : iR ⁻¹' S,
      f ⟨iR b.1, b.2⟩ = jTR (fR b))
    (history : List (Set P))
    (hHistL : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) fL history)
    (hHistR : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR history)
    (pG : G → P)
    (hRootL : ∀ (a : iL ⁻¹' S) g,
      fL a = sTL g → pL a.1 = pG g)
    (hRootR : ∀ (b : iR ⁻¹' S) g,
      fR b = sTR g → pR b.1 = pG g) :
    SetRespectsProjectedHistory pWhole S f history := by
  have hHistL' : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) (jTL ∘ fL) history := by
    intro K hK a b hab
    exact hHistL K hK a b (jTL.injective hab)
  have hHistR' : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) (jTR ∘ fR) history := by
    intro K hK a b hab
    exact hHistR K hK a b (jTR.injective hab)
  have hCross : ∀ (a : iL ⁻¹' S) (b : iR ⁻¹' S),
      (jTL ∘ fL) a = (jTR ∘ fR) b →
      pL a.1 = pR b.1 := by
    intro a b hab
    exact hTgt.crossKernel_of_targetRootProjection
      fL fR (fun a => pL a.1) (fun b => pR b.1)
      pG hRootL hRootR a b hab
  exact hSrc.setRespectsProjectedHistory_glue_crossKernel
    S pWhole pL pR hpL hpR f
    (jTL ∘ fL) (jTR ∘ fR) hfL hfR
    history hHistL' hHistR' hCross

end StructuralRamsey.Structure.IsFreeAmalgam

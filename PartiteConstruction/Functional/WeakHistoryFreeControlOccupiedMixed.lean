import PartiteConstruction.Functional.WeakHistoryFreeMarkedTreeGlue
import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory

/-!
# Track D: ordinary control predecessor supplies the occupied A marks

English proof was committed FIRST in
docs/track-d-english-historyfree-exact-weak-functional-glue-20261112.md
(on parent PR #640).

An unprotected `SetAmbientRelativeWeakTreeWitness` of the exact
CONTROL image of a weak source test already contains a FULL target
A mark for every selected full alpha:A ↪ D. Pull back the weak map
and all ACTUAL ambient A-copy certificates along the source EHN
projection, retaining that selected target mark. The only necessary
root condition is OCCUPIED alpha-label agreement.

Use the resulting two marked SIDE weak witnesses and the genuine
native full-functional source free diagram to produce a strict
full-function B-tree witness for the exact MIXED weak source test,
with ambient A-copy protection. NO projected history is claimed.

This is the positive mixed-step constructor for a strictly WEAKER
candidate invariant. It neither expands a weak test to a closure
hull nor assumes an injective/colliding source root map.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA E P VB : Type v}

/-- An ORDINARY (not protected) control weak B-tree certificate,
pulled back along an actual EHN map on an exact weak source set,
retains a FULL target mark of any selected alpha:A↪D.

The mark is required to agree with the source map ONLY at
OCCUPIED source vertices with control part alpha(a).
Extra target A-mark hits by other vertices are explicitly allowed.
-/
theorem SetAmbientRelativeWeakTreeWitness.pullback_ehn_with_occupied_mark
    {A : Structure L UA} (hA : A.Irreducible)
    {Side : Structure L E} {D : Structure L P}
    (alpha : Embedding A D)
    {p : E → P}
    (hp : Side.IsEHNHomomorphismEmbedding D p)
    (Base : Structure L VB)
    (S : Set E)
    (hControl : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (p '' S) []) :
    ∃ (Y : Type v) (Target : Structure L Y),
      TreeAmalgam Base Y Target ∧
      ∃ f : S → Y,
        IsAmbientRelativeWeakHE Side S Target f ∧
        SetAmbientACopyIntersections A Side Target S f ∧
        ∃ mark : Embedding A Target,
          mark.ContainedInIrreducible ∧
          ∀ (x : S) (a : UA),
            p x.1 = alpha a → f x = mark a := by
  classical
  obtain ⟨Y, Target, hTree, g, hWeakD, hCopiesD, _hHistory⟩ :=
    hControl
  obtain ⟨mark, hMark, hMarkAgree⟩ := hCopiesD alpha
  let pS : S → p '' S :=
    fun x => ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  let f : S → Y := g ∘ pS
  have hWeak : IsAmbientRelativeWeakHE Side S Target f :=
    hWeakD.pullback_ehn_exact hp S g
  have hCopies : SetAmbientACopyIntersections A Side Target S f := by
    intro e
    obtain ⟨eD, heD⟩ := hp.2 A hA e
    obtain ⟨eT, hContains, hAgrees⟩ := hCopiesD eD
    refine ⟨eT, hContains, ?_⟩
    intro a ha
    have haD : eD a ∈ p '' S := by
      rw [heD a]
      exact ⟨e a, ha, rfl⟩
    calc
      eT a = g ⟨eD a, haD⟩ := hAgrees a haD
      _ = f ⟨e a, ha⟩ := by
        change g (⟨eD a, haD⟩ : p '' S) =
          g (pS ⟨e a, ha⟩)
        congr 1
        apply Subtype.ext
        exact heD a
  have hAnchor (x : S) (a : UA)
      (hLabel : p x.1 = alpha a) :
      f x = mark a := by
    have hmem : alpha a ∈ p '' S := by
      rw [← hLabel]
      exact ⟨x.1, x.2, rfl⟩
    calc
      f x = g ⟨alpha a, hmem⟩ := by
        apply congrArg g
        apply Subtype.ext
        exact hLabel
      _ = mark a := (hMarkAgree a hmem).symm
  exact ⟨Y, Target, hTree, f, hWeak, hCopies,
    mark, hMark, hAnchor⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA H E F C VB P : Type v}

/-- For a TRUE full native functional source free amalgam, the ORDINARY
control strict weak-tree witnesses for the exact projected side sets
already give a STRICT functional weak-tree witness of the exact whole
weak S, protecting genuine ambient A-copy intersections.

The source root's projection into A may COLLIDE; only FULL TARGET
A marks are glued. There is no closedness assumption on weak S,
either side weak set, or the two projected control images.

NO arbitrary projected histories are transferred. -/
theorem ambientRelativeWeakTree_noHistory_of_ordinaryControlSideImages
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (D : Structure L P) (alpha : Embedding A D)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpWholeL : ∀ a, pWhole (iL a) = pL a)
    (hpWholeR : ∀ b, pWhole (iR b) = pR b)
    (hpL : Left.IsEHNHomomorphismEmbedding D pL)
    (hpR : Right.IsEHNHomomorphismEmbedding D pR)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, pWhole (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (hControlL : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P)
      (pL '' (iL ⁻¹' S)) [])
    (hControlR : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P)
      (pR '' (iR ⁻¹' S)) []) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole pWhole S [] := by
  classical
  obtain ⟨YL, TL, hTL, fL, hWeakL, hCopiesL,
      markL, hcL, hAnchorL⟩ :=
    SetAmbientRelativeWeakTreeWitness.pullback_ehn_with_occupied_mark
      hA alpha hpL Base (iL ⁻¹' S) hControlL
  obtain ⟨YR, TR, hTR, fR, hWeakR, hCopiesR,
      markR, hcR, hAnchorR⟩ :=
    SetAmbientRelativeWeakTreeWitness.pullback_ehn_with_occupied_mark
      hA alpha hpR Base (iR ⁻¹' S) hControlR
  let q : ((iL.comp sL) ⁻¹' S) → UA :=
    fun x => Classical.choose (hRootAlpha x.1)
  have hRootL (d : H) (hdL : iL (sL d) ∈ S) :
      fL ⟨sL d, hdL⟩ = markL (q ⟨d, hdL⟩) := by
    have hLabel : pL (sL d) = alpha (q ⟨d, hdL⟩) :=
      (hpWholeL (sL d)).symm.trans
        (Classical.choose_spec (hRootAlpha d))
    exact hAnchorL ⟨sL d, hdL⟩ (q ⟨d, hdL⟩) hLabel
  have hRootR (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S) :
      fR ⟨sR d, hdR⟩ = markR (q ⟨d, hdL⟩) := by
    have hOverlap : iL (sL d) = iR (sR d) :=
      (hSrc.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
    have hLabel : pR (sR d) = alpha (q ⟨d, hdL⟩) := by
      calc
        pR (sR d) = pWhole (iR (sR d)) :=
          (hpWholeR (sR d)).symm
        _ = pWhole (iL (sL d)) :=
          congrArg pWhole hOverlap.symm
        _ = alpha (q ⟨d, hdL⟩) :=
          Classical.choose_spec (hRootAlpha d)
    exact hAnchorR ⟨sR d, hdR⟩ (q ⟨d, hdL⟩) hLabel
  obtain ⟨Y, Target, hTree, f, hWeak, hCopies⟩ :=
    hSrc.ambientRelativeWeakTree_noHistory_glue_markedRoot
      hA S Base TL TR hTL hTR markL markR hcL hcR
      fL fR hWeakL hWeakR q hRootL hRootR hCopiesL hCopiesR
  refine ⟨Y, Target, hTree, f, hWeak, hCopies, ?_⟩
  intro K hK
  simp at hK

end StructuralRamsey.Structure.IsFreeAmalgam

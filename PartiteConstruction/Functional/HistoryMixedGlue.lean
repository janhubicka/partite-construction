import PartiteConstruction.Functional.RelativeHistoryTreeCompletion
import PartiteConstruction.Functional.IsolatedCommonLabelGlue

/-! # Mixed functional gluing from relative history witnesses

A closed functional mixed step has a genuine source free-amalgam
decomposition.  If the two sides can realize the common overlap with the same
embedded A-labels, the isolated common-label glue gives a full
homomorphism-embedding of the whole source into a genuine tree amalgam.

For later steps we retain both finite diaries.  Projected diary sets are
carried as their source preimages during the glue, then decoded back to the
projection after gluing.
-/

namespace StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike

universe u v

variable {L : Language.{u}}
variable {U P V H E F C : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {Base : Structure L V}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Glue two whole-side relative-history witnesses over one common embedded
A-boundary.  The conclusion retains both finite history families. -/
theorem glueWholeWitnesses
    (hA : A.Irreducible)
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (p : C → P)
    (β : Embedding A D)
    (ell : Embedding Root A)
    (hprojL : ∀ x, p (iL (sL x)) = β (ell x))
    (hprojR : ∀ x, p (iR (sR x)) = β (ell x))
    {n : ℕ}
    [Fintype E] [Fintype F]
    (hLeft :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := Left) (Base := Base)
        (p ∘ iL) n)
    (hRight :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := Right) (Base := Base)
        (p ∘ iR) n)
    (hgenL : Left.GeneratedByAtMost n)
    (hgenR : Right.GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set C)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C → Z,
        Whole.IsHomomorphismEmbedding Target f ∧
        (∀ Hset ∈ projectedHistory, ∀ x y : C,
          f x = f y → (p x ∈ Hset ↔ p y ∈ Hset)) ∧
        (∀ Hset ∈ sourceHistory, ∀ x y : C,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) := by
  classical
  let history : List (Set C) :=
    sourceHistory ++ projectedHistory.map (fun Hset => p ⁻¹' Hset)
  let historyL : List (Set E) :=
    history.map (fun Hset => iL ⁻¹' Hset)
  let historyR : List (Set F) :=
    history.map (fun Hset => iR ⁻¹' Hset)

  obtain ⟨ZL, TL, hTreeL, fL, hfL, _hPartL, _hProjL, hHistL0,
    targetL, hcompatL, hisoL⟩ :=
    hLeft.fullWitness_embeddedLabels
      hgenL [] historyL ell β sL
      (fun x => hprojL x)

  obtain ⟨ZR, TR, hTreeR, fR, hfR, _hPartR, _hProjR, hHistR0,
    targetR, hcompatR, hisoR⟩ :=
    hRight.fullWitness_embeddedLabels
      hgenR [] historyR ell β sR
      (fun x => hprojR x)

  have hrootL :
      IsFreeAmalgam.RootIsolated sL targetL ell fL := by
    intro x a hxa
    obtain ⟨d, hxd, hda⟩ := hisoL x a hxa
    exact ⟨d, hxd, hda⟩

  have hrootR :
      IsFreeAmalgam.RootIsolated sR targetR ell fR := by
    intro x a hxa
    obtain ⟨d, hxd, hda⟩ := hisoR x a hxa
    exact ⟨d, hxd, hda⟩

  have hHistL :
      ∀ Hset ∈ history, ∀ x y : E,
        fL x = fL y → (iL x ∈ Hset ↔ iL y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hpre :
        iL ⁻¹' Hset ∈ historyL := by
      apply List.mem_map.mpr
      exact ⟨Hset, hmem, rfl⟩
    exact hHistL0 (iL ⁻¹' Hset) hpre x y hxy

  have hHistR :
      ∀ Hset ∈ history, ∀ x y : F,
        fR x = fR y → (iR x ∈ Hset ↔ iR y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hpre :
        iR ⁻¹' Hset ∈ historyR := by
      apply List.mem_map.mpr
      exact ⟨Hset, hmem, rfl⟩
    exact hHistR0 (iR ⁻¹' Hset) hpre x y hxy

  obtain ⟨Z, Target, hTree, f, hf, hHist⟩ :=
    LocallyClosedTreeCompletable.glueIsolatedCommonLabels_withSourceHistory
      (Base := Base) hA hSrc hTreeL hTreeR
      targetL targetR ell ell.injective
      fL fR hcompatL hcompatR hfL hfR
      hrootL hrootR history hHistL hHistR

  have hProj :
      ∀ Hset ∈ projectedHistory, ∀ x y : C,
        f x = f y → (p x ∈ Hset ↔ p y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hpre :
        p ⁻¹' Hset ∈ history := by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨Hset, hmem, rfl⟩)
    simpa using hHist (p ⁻¹' Hset) hpre x y hxy

  have hSrcHist :
      ∀ Hset ∈ sourceHistory, ∀ x y : C,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hwhole : Hset ∈ history := by
      apply List.mem_append.mpr
      exact Or.inl hmem
    exact hHist Hset hwhole x y hxy

  exact ⟨Z, Target, hTree, f, hf, hProj, hSrcHist⟩

end StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike

import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue
import PartiteConstruction.Functional.OriginalPartialRelativeAppend

/-!
# Track D: a genuinely colliding source root can glue via a FULL target mark

English proof and adversarial scope:
docs/track-d-english-colliding-marked-target-glue-20261112.md

The common full source separator R may have a NONINJECTIVE map q:R → A.
The two original-2019 PARTIAL side maps are required to factor through
the SAME q, but only after full TARGET marks A ↪ T_L and A ↪ T_R.
Glue the target trees along A, never along the non-full map q or a
generated closure substituted for the exact source weak test.

This proves (i) absolute source gluing, (ii) an incoming old-side
relative extension over the already chosen left target, and (iii)
one-step preservation of a separate earlier strict target anchor.
It does NOT produce the aligned marks from a general ordered
Hales–Jewett history or solve the unrestricted n-pass rank increment.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA H E F Z VB YL YR G0 H0 : Type v}

/-- Two original-partial strict side completions glue over an arbitrary
FULL marked target A-copy, even if the ACTUAL source-root map q:R→A
is reducible, many-generated, and noninjective.

Only the TARGET A→T maps must be full/function-closed and contained in
irreducible B-pieces. Neither side map needs to be full globally, nor
do we assert any full source-root embedding into B. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_of_marked_partialSides_noninjective
    {A : Structure L UA} {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (TL : Structure L YL) (TR : Structure L YR)
    (hTL : TreeAmalgam Base YL TL)
    (hTR : TreeAmalgam Base YR TR)
    (markL : Embedding A TL) (markR : Embedding A TR)
    (hMarkL : markL.ContainedInIrreducible)
    (hMarkR : markR.ContainedInIrreducible)
    (q : H → UA)
    (pL : E → YL) (pR : F → YR)
    (hpL : Left.IsOriginalPartialHomomorphismEmbedding TL pL)
    (hpR : Right.IsOriginalPartialHomomorphismEmbedding TR pR)
    (hRootL : ∀ x : H, pL (sL x) = markL (q x))
    (hRootR : ∀ x : H, pR (sR x) = markR (q x)) :
    HasOriginalPartialTreeCompletion Base Whole := by
  let Target := FreeAmalgam.amalgam A TL TR markL markR
  let jL := FreeAmalgam.leftEmbedding A TL TR markL markR
  let jR := FreeAmalgam.rightEmbedding A TL TR markL markR
  have hTarget : IsFreeAmalgam markL markR jL jR :=
    FreeAmalgam.isFreeAmalgam A TL TR markL markR
  have hTree : TreeAmalgam Base _ Target :=
    FreeAmalgam.treeAmalgam A TL TR markL markR
      Base hTL hTR hMarkL hMarkR
  have hpLeft : Left.IsEHNHomomorphismEmbedding
      Target (jL ∘ pL) :=
    jL.isEHNHomomorphismEmbedding.comp hpL.toEHN
  have hpRight : Right.IsEHNHomomorphismEmbedding
      Target (jR ∘ pR) :=
    jR.isEHNHomomorphismEmbedding.comp hpR.toEHN
  have hAgree : ∀ x : H,
      (jL ∘ pL) (sL x) = (jR ∘ pR) (sR x) := by
    intro x
    change jL (pL (sL x)) = jR (pR (sR x))
    rw [hRootL x, hRootR x]
    exact (hTarget.overlap (markL (q x)) (markR (q x))).mpr
      ⟨q x, rfl, rfl⟩
  obtain ⟨p, hp, _hL, _hR⟩ :=
    hSrc.exists_EHN_projection
      (jL ∘ pL) (jR ∘ pR) hpLeft hpRight hAgree
  exact ⟨_, Target, hTree, p, hp.toOriginalPartial⟩

/-- A marked RIGHT-side ORIGINAL-PARTIAL strict B-tree completion is a
strict relative extension over an ALREADY CHOSEN strict left target
Start, with a possibly NONINJECTIVE original source-root map.

The marked gluing root A is full in BOTH TARGETS; the source root need
not embed fully into A or Base. This is the incoming-copy completion
interface used by originalPartialTreeExtension_append. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_marked_partial_right_noninjective
    {A : Structure L UA} {Root : Structure L H}
    {Right : Structure L F}
    (Base : Structure L VB)
    (Start : Structure L YL)
    (hStart : TreeAmalgam Base YL Start)
    (markStart : Embedding A Start)
    (hMarkStart : markStart.ContainedInIrreducible)
    (TR : Structure L YR)
    (hTR : TreeAmalgam Base YR TR)
    (markR : Embedding A TR)
    (hMarkR : markR.ContainedInIrreducible)
    (sR : Embedding Root Right)
    (q : H → UA)
    (pR : F → YR)
    (hpR : Right.IsOriginalPartialHomomorphismEmbedding TR pR)
    (hRootR : ∀ x : H, pR (sR x) = markR (q x)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base sR (markStart ∘ q) := by
  let Target := FreeAmalgam.amalgam A Start TR markStart markR
  let jL := FreeAmalgam.leftEmbedding A Start TR markStart markR
  let jR := FreeAmalgam.rightEmbedding A Start TR markStart markR
  have hTarget : IsFreeAmalgam markStart markR jL jR :=
    FreeAmalgam.isFreeAmalgam A Start TR markStart markR
  let ext : TreeExtension Base Start _ Target :=
    TreeExtension.attachTree TreeExtension.refl
      hTR markStart markR hMarkStart hMarkR
  have hpTarget : Right.IsOriginalPartialHomomorphismEmbedding
      Target (jR ∘ pR) :=
    jR.isEHNHomomorphismEmbedding.toOriginalPartial.comp hpR
  refine ⟨_, Target, ext, jR ∘ pR, hpTarget, ?_⟩
  intro x
  change jR (pR (sR x)) = ext.startEmbedding (markStart (q x))
  rw [hRootR x]
  change jR (markR (q x)) = jL (markStart (q x))
  exact ((hTarget.overlap (markStart (q x)) (markR (q x))).mpr
    ⟨q x, rfl, rfl⟩).symm

/-- One-step historical append: keep the ORIGINAL previous target Start0
and its designated source anchor, and attach an incoming old copy via a
test-dependent marked target A. The source-root map q:R→A may COLLIDE.
The full target marks must be provided and already aligned; the
statement does not fabricate them from unrelated absolute completions.
-/
theorem IsFreeAmalgam.originalPartialTreeExtension_append_marked_noninjective
    {A : Structure L UA}
    {Anchor0 : Structure L H0}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (Start0 : Structure L G0)
    (hStart0 : TreeAmalgam Base G0 Start0)
    (anchor : Embedding Anchor0 Left)
    (q0 : H0 → G0)
    (TLeft : Structure L YL)
    (hExtL : TreeExtension Base Start0 YL TLeft)
    (pLeft : E → YL)
    (hpLeft : Left.IsOriginalPartialHomomorphismEmbedding TLeft pLeft)
    (hAnchor : ∀ x : H0,
      pLeft (anchor x) = hExtL.startEmbedding (q0 x))
    (markLeft : Embedding A TLeft)
    (hMarkLeft : markLeft.ContainedInIrreducible)
    (q : H → UA)
    (hRootLeft : ∀ x : H, pLeft (sL x) = markLeft (q x))
    (TR : Structure L YR)
    (hTR : TreeAmalgam Base YR TR)
    (markRight : Embedding A TR)
    (hMarkRight : markRight.ContainedInIrreducible)
    (pRight : F → YR)
    (hpRight : Right.IsOriginalPartialHomomorphismEmbedding TR pRight)
    (hRootRight : ∀ x : H, pRight (sR x) = markRight (q x)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start0) Base (iL.comp anchor) q0 := by
  have hTreeLeft : TreeAmalgam Base YL TLeft :=
    hExtL.toTree hStart0
  have hRight : HasOriginalPartialTreeExtensionCompletion
      (Start := TLeft) Base sR (pLeft ∘ sL) := by
    have hMarkRight :
        HasOriginalPartialTreeExtensionCompletion
          (Start := TLeft) Base sR (markLeft ∘ q) :=
      HasOriginalPartialTreeExtensionCompletion.of_marked_partial_right_noninjective
        Base TLeft hTreeLeft markLeft hMarkLeft
        TR hTR markRight hMarkRight
        sR q pRight hpRight hRootRight
    have hRootEq : (pLeft ∘ sL) = (markLeft ∘ q) := by
      funext x
      exact hRootLeft x
    rw [hRootEq]
    exact hMarkRight
  exact hSrc.originalPartialTreeExtension_append
    Base Start0 anchor q0 TLeft hExtL pLeft hpLeft hAnchor hRight

end StructuralRamsey.Structure

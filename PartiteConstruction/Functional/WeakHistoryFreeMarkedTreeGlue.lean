import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue
import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.AmbientRelativeWeakPullback

/-!
# Track D: weaken the native strict functional mixed-tree invariant

English proof FIRST:
docs/track-d-english-historyfree-exact-weak-functional-glue-20261112.md

The genuine native mixed weak step does NOT require the forward
no-wrong-hit half of ProtectedAMark if we only want a STRICT tree,
an ambient-relative weak HE on the EXACT tested vertex set, and
protection of all real FULL ambient A-copy intersections.
Those three properties can be preserved by gluing two side target
strict trees over full A marks which agree on the OCCUPIED source root.

This omits arbitrary projected-history diaries. Their preservation
remains the distinct stronger open requirement. The result below
allows a nonclosed weak S and a noninjective source-root A map;
ONLY the gluing TARGET marks are full.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA H E F C VB WL WR P : Type v}

/-- Strict native set-valued-function weak-test gluing over full TARGET
A-marks, with NO history and NO protected mark/no-wrong-hit premise.

The source common root is a genuine full-functional root but its
intersection with the exact weak S need not be closed or irreducible.
The occupied root can map noninjectively to A. The two completed side
maps may be noninjective outside every irreducible source test.

The output retains:
(1) a strict full-functional B-tree target,
(2) an ambient-relative weak HE on EXACT S,
(3) full protected copies of every real AMBIENT irreducible A-test.
It deliberately omits projected-history coherence. -/
theorem ambientRelativeWeakTree_noHistory_glue_markedRoot
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (Base : Structure L VB)
    (TL : Structure L WL) (TR : Structure L WR)
    (hTreeL : TreeAmalgam Base WL TL)
    (hTreeR : TreeAmalgam Base WR TR)
    (markL : Embedding A TL) (markR : Embedding A TR)
    (hcL : markL.ContainedInIrreducible)
    (hcR : markR.ContainedInIrreducible)
    (fL : (iL ⁻¹' S) → WL)
    (fR : (iR ⁻¹' S) → WR)
    (hL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S) TL fL)
    (hR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S) TR fR)
    (q : ((iL.comp sL) ⁻¹' S) → UA)
    (hRootL : ∀ (d : H) (hdL : iL (sL d) ∈ S),
      fL ⟨sL d, hdL⟩ = markL (q ⟨d, hdL⟩))
    (hRootR : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fR ⟨sR d, hdR⟩ = markR (q ⟨d, hdL⟩))
    (hCopiesL : SetAmbientACopyIntersections A Left TL
      (iL ⁻¹' S) fL)
    (hCopiesR : SetAmbientACopyIntersections A Right TR
      (iR ⁻¹' S) fR) :
    ∃ (Y : Type v) (Target : Structure L Y),
      TreeAmalgam Base Y Target ∧
      ∃ f : S → Y,
        IsAmbientRelativeWeakHE Whole S Target f ∧
        SetAmbientACopyIntersections A Whole Target S f := by
  classical
  let Target := FreeAmalgam.amalgam A TL TR markL markR
  let jL := FreeAmalgam.leftEmbedding A TL TR markL markR
  let jR := FreeAmalgam.rightEmbedding A TL TR markL markR
  have hTgt : IsFreeAmalgam markL markR jL jR :=
    FreeAmalgam.isFreeAmalgam A TL TR markL markR
  have hTree : TreeAmalgam Base _ Target :=
    FreeAmalgam.treeAmalgam A TL TR markL markR Base
      hTreeL hTreeR hcL hcR
  have hWeakL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S)
      Target (jL ∘ fL) :=
    hL.postcomp_full jL
  have hWeakR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S)
      Target (jR ∘ fR) :=
    hR.postcomp_full jR
  have hAgree : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      (jL ∘ fL) ⟨sL d, hdL⟩ =
      (jR ∘ fR) ⟨sR d, hdR⟩ := by
    intro d hdL hdR
    change jL (fL ⟨sL d, hdL⟩) =
      jR (fR ⟨sR d, hdR⟩)
    rw [hRootL d hdL, hRootR d hdL hdR]
    exact (hTgt.overlap (markL (q ⟨d, hdL⟩))
      (markR (q ⟨d, hdL⟩))).mpr
      ⟨q ⟨d, hdL⟩, rfl, rfl⟩
  obtain ⟨f, hWeak, hfL, hfR⟩ :=
    hSrc.ambientRelativeWeakHE_glue S Target
      (jL ∘ fL) (jR ∘ fR) hWeakL hWeakR hAgree
  have hCopies : SetAmbientACopyIntersections
      A Whole Target S f :=
    hSrc.ambientACopyIntersections_glue
      hA S Target f (jL ∘ fL) (jR ∘ fR)
      hfL hfR
      (hCopiesL.postcomp_full jL)
      (hCopiesR.postcomp_full jR)
  exact ⟨_, Target, hTree, f, hWeak, hCopies⟩

end StructuralRamsey.Structure.IsFreeAmalgam

import PartiteConstruction.Functional.LabelledWeakTreeHistoryGlue
import PartiteConstruction.Functional.WeakProjectedHistoryCrossKernelGlue

/-!
# Protected marked A-collars for strict functional weak-tree gluing

This is the audited *conditional* mixed step for the native Appendix A
iteration, in the genuine SET-VALUED FUNCTION language.

An exact weak test S is accompanied by a marked FULL A-copy aT:A↪T
in its strict B-tree completion f:S→T. Its *protected trace* says
  f(s)=aT(a)  IFF  p(s)=alpha(a)
for each tested vertex and each a∈A. The forward implication
prohibits accidental hits by vertices outside the projected A-boundary;
ordinary projected histories do NOT imply it. The reverse implication
provides the prescribed root alignment.

Two weak side witnesses with protected traces on the SAME alpha can be
glued over their FULL marked A-copies. These roots are function-closed
because the maps are full embeddings; they are contained in genuine
irreducible B-constituents of both strict tree targets.

We use the previously checked source weak-HE gluing, ambient A-copy
control, and cross-kernel history lemma. Unlike the stronger labelled
approach, NO EHN label map on every target B-tree vertex is required.
For a genuinely closed source test the resulting weak map upgrades to
the original-2019 partial homomorphism-embedding by the existing lemma.

The main remaining problem is to CONSTRUCT protected-trace witnesses
for predecessor tests in arbitrary actual Hales-Jewett attachment
histories, not the conditional gluing formalized here.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA P C Z : Type v}

/-- A marked full A-copy in an exact weak-test target has EXACTLY
the tested vertices bearing its prescribed alpha labels.

The reverse direction is labelled *anchoring*; the forward direction
is *no wrong hit*. Both are needed for the functional mixed proof. -/
def ProtectedAMark
    {A : Structure L UA} {D : Structure L P}
    {Target : Structure L Z}
    (alpha : Embedding A D)
    (part : C → P) (S : Set C) (f : S → Z)
    (mark : Embedding A Target) : Prop :=
  ∀ x : S, ∀ a : UA, f x = mark a ↔ part x.1 = alpha a

/-- A target-side label map is SUFFICIENT for no-wrong-hit safety,
provided an independently checked anchoring condition holds.
The full global target EHN hypothesis used elsewhere is stronger
than necessary here: the equalities on the tested and marked points
alone suffice. -/
theorem ProtectedAMark.of_labelled
    {A : Structure L UA} {D : Structure L P}
    {Target : Structure L Z}
    (alpha : Embedding A D)
    (part : C → P) (S : Set C) (f : S → Z)
    (mark : Embedding A Target)
    (t : Z → P)
    (hTest : ∀ x : S, t (f x) = part x.1)
    (hMark : ∀ a, t (mark a) = alpha a)
    (hAnchor : ∀ (x : S) (a : UA),
      part x.1 = alpha a → f x = mark a) :
    ProtectedAMark alpha part S f mark := by
  intro x a
  constructor
  · intro hHit
    calc
      part x.1 = t (f x) := (hTest x).symm
      _ = t (mark a) := congrArg t hHit
      _ = alpha a := hMark a
  · exact hAnchor x a

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA H E F C VB P WL WR : Type v}

/-- Two strict full-functional B-tree witnesses over exact weak
source sides can be glued over their protected FULL A-collars.

The source common root need NOT be function-closed as a weak test,
and need NOT be irreducible. Only its projection is assumed to lie
inside the same alpha(A); the FULL underlying source amalgam keeps
closed roots as required.

The preserved conclusion comprises:
  * a STRICT full-functional B-tree target,
  * an ambient-relative weak HE on EXACT tested vertices,
  * every ACTUAL full ambient A-intersection,
  * all supplied finite projected histories.

No global target EHN labelling, no singleton functions, no weak-set
closure enlargement, and no false arbitrary-stage existence claim. -/
theorem protectedAMarkWeakTree_glue
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    {D : Structure L P}
    (alpha : Embedding A D)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpL : ∀ a, pWhole (iL a) = pL a)
    (hpR : ∀ b, pWhole (iR b) = pR b)
    (hRootAlpha : ∀ d : H, ∃ a : UA,
      pWhole (iL (sL d)) = alpha a)
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
    (hTraceL : ProtectedAMark alpha pL (iL ⁻¹' S) fL markL)
    (hTraceR : ProtectedAMark alpha pR (iR ⁻¹' S) fR markR)
    (hCopiesL : SetAmbientACopyIntersections A Left TL
      (iL ⁻¹' S) fL)
    (hCopiesR : SetAmbientACopyIntersections A Right TR
      (iR ⁻¹' S) fR)
    (history : List (Set P))
    (hHistL : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) fL history)
    (hHistR : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR history) :
    SetAmbientRelativeWeakTreeWitness A Base Whole pWhole S history := by
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
    let a : UA := Classical.choose (hRootAlpha d)
    have hAlpha : pWhole (iL (sL d)) = alpha a :=
      Classical.choose_spec (hRootAlpha d)
    have hLabelL : pL (sL d) = alpha a :=
      (hpL (sL d)).symm.trans hAlpha
    have hRootEq : iL (sL d) = iR (sR d) :=
      (hSrc.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
    have hLabelR : pR (sR d) = alpha a := by
      calc
        pR (sR d) = pWhole (iR (sR d)) := (hpR (sR d)).symm
        _ = pWhole (iL (sL d)) := congrArg pWhole hRootEq.symm
        _ = alpha a := hAlpha
    have hfl : fL ⟨sL d, hdL⟩ = markL a :=
      (hTraceL ⟨sL d, hdL⟩ a).2 hLabelL
    have hfr : fR ⟨sR d, hdR⟩ = markR a :=
      (hTraceR ⟨sR d, hdR⟩ a).2 hLabelR
    change jL (fL ⟨sL d, hdL⟩) =
      jR (fR ⟨sR d, hdR⟩)
    rw [hfl, hfr]
    exact (hTgt.overlap (markL a) (markR a)).mpr
      ⟨a, rfl, rfl⟩
  obtain ⟨f, hWeak, hfL, hfR⟩ :=
    hSrc.ambientRelativeWeakHE_glue S Target
      (jL ∘ fL) (jR ∘ fR) hWeakL hWeakR hAgree
  have hCopies : SetAmbientACopyIntersections A Whole Target S f :=
    hSrc.ambientACopyIntersections_glue hA S Target f
      (jL ∘ fL) (jR ∘ fR) hfL hfR
      (hCopiesL.postcomp_full jL)
      (hCopiesR.postcomp_full jR)
  have hFactorL : ∀ (x : iL ⁻¹' S) (a : UA),
      fL x = markL a → pL x.1 = alpha a := by
    intro x a hx
    exact (hTraceL x a).1 hx
  have hFactorR : ∀ (x : iR ⁻¹' S) (a : UA),
      fR x = markR a → pR x.1 = alpha a := by
    intro x a hx
    exact (hTraceR x a).1 hx
  have hHist : SetRespectsProjectedHistory pWhole S f history :=
    hSrc.setRespectsProjectedHistory_glue_targetRoot
      S pWhole pL pR hpL hpR hTgt
      f fL fR hfL hfR history hHistL hHistR
      (fun a => alpha a) hFactorL hFactorR
  exact ⟨_, Target, hTree, f, hWeak, hCopies, hHist⟩

end StructuralRamsey.Structure.IsFreeAmalgam

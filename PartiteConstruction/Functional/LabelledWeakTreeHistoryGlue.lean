import PartiteConstruction.Functional.LabelledStrictFunctionalTreeGlue
import PartiteConstruction.Functional.AmbientACopyIntersectionsGlue
import PartiteConstruction.Functional.AmbientRelativeWeakAmalgamGlue
import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory

/-!
# Marked-A gluing of LABELLED strict functional weak-test completions

This is an alternative constructive interface for the hard mixed case
of the genuinely functional iterated Hales-Jewett Picture, inspired by
the verified relational U-closed/partite method but staying entirely
in the natural set-valued function language.

Suppose two strict full-functional B-tree completions of the exact
weak sides are EQUIPPED with:
* full EHN projections into the SAME closed control D;
* marked FULL A-copies contained in irreducible B constituents, whose
  target labels are the SAME actual embedding alpha:A↪D;
* ambient-relative weak HEs from the two exact weak source sides,
  commuting pointwise with their outer part projections;
* A-copy intersection certificates for every ACTUAL full source A-copy;
* identical marked-A values on the actual exact weak source root.

Then glue the two target B-trees over the FULL marked A-copies. The
verified labelled-target free-amalgam construction automatically gives
a common EHN control projection, hence TRANSVERSAL output fibres.
The source weak-side maps glue by the verified function-language lemma.
Since the final target map COMMUTES with the source part projection,
it preserves ALL finite projected history predicates automatically,
without an independent pG, target-root isolation, or arbitrary
global injectivity of source parts.

This is not the false arbitrary-stage C5 extension schema: it ASSUMES
the two side witnesses have the stated compatible marked A-copies
and EHN target labels. Existence of these stronger labelled
side witnesses in the actual maximal-rank mixed HJ attachment is the
substantive remaining obligation. No function closure hull, no
relational surrogate picture, and no singleton-valuedness is used.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {VA H E F C VB P WL WR : Type v}

/-- Two strict FULL-functional labelled B-tree witnesses glue over their
marked full A-copies, with their source maps agreeing on the exact weak
common root. The combined target remains an EHN-labelled strict B-tree;
all individual set-valued function fibres are automatically transversal.

The output includes the full ambient-relative weak HE, protection of
all actual ambient full A-copy intersections, and ALL finite projected
history predicates—those histories need not even be supplied on the sides,
as the total target control projection makes them automatic.

This is a CONDITIONAL construction. The difficult maximal mixed case
must still produce such marked labelled side completions. -/
theorem labelledStrictTreeWeakHistory_glue_markedA
    {A : Structure L VA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (D : Structure L P)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpL : ∀ a, pWhole (iL a) = pL a)
    (hpR : ∀ b, pWhole (iR b) = pR b)
    (Base : Structure L VB)
    (TL : Structure L WL) (TR : Structure L WR)
    (hTreeL : TreeAmalgam Base WL TL)
    (hTreeR : TreeAmalgam Base WR TR)
    (α : Embedding A D)
    (aTL : Embedding A TL) (aTR : Embedding A TR)
    (hcTL : aTL.ContainedInIrreducible)
    (hcTR : aTR.ContainedInIrreducible)
    (tL : WL → P) (tR : WR → P)
    (htL : TL.IsEHNHomomorphismEmbedding D tL)
    (htR : TR.IsEHNHomomorphismEmbedding D tR)
    (hMarkL : ∀ a, tL (aTL a) = α a)
    (hMarkR : ∀ a, tR (aTR a) = α a)
    (fL : (iL ⁻¹' S) → WL)
    (fR : (iR ⁻¹' S) → WR)
    (hL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S) TL fL)
    (hR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S) TR fR)
    (hfLabelsL : ∀ a : iL ⁻¹' S, tL (fL a) = pL a.1)
    (hfLabelsR : ∀ b : iR ⁻¹' S, tR (fR b) = pR b.1)
    (q : ((iL.comp sL) ⁻¹' S) → VA)
    (hRootL : ∀ (d : H) (hdL : iL (sL d) ∈ S),
      fL ⟨sL d, hdL⟩ = aTL (q ⟨d, hdL⟩))
    (hRootR : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fR ⟨sR d, hdR⟩ = aTR (q ⟨d, hdL⟩))
    (hCopiesL : SetAmbientACopyIntersections A Left TL
      (iL ⁻¹' S) fL)
    (hCopiesR : SetAmbientACopyIntersections A Right TR
      (iR ⁻¹' S) fR)
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ t : Z → P,
        Target.IsEHNHomomorphismEmbedding D t ∧
        ∃ f : S → Z,
          IsAmbientRelativeWeakHE Whole S Target f ∧
          SetAmbientACopyIntersections A Whole Target S f ∧
          (∀ x : S, t (f x) = pWhole x.1) ∧
          SetRespectsProjectedHistory pWhole S f history ∧
          (∀ F (x : Fin (L.funcArity F) → Z),
            Set.InjOn t (Target.func F x)) := by
  classical
  let Target := FreeAmalgam.amalgam A TL TR aTL aTR
  let jL := FreeAmalgam.leftEmbedding A TL TR aTL aTR
  let jR := FreeAmalgam.rightEmbedding A TL TR aTL aTR
  have hTargetFree : IsFreeAmalgam aTL aTR jL jR :=
    FreeAmalgam.isFreeAmalgam A TL TR aTL aTR
  have hLabelAgree : ∀ a, tL (aTL a) = tR (aTR a) := by
    intro a
    exact (hMarkL a).trans (hMarkR a).symm
  obtain ⟨t, hTree, ht, htLeft, htRight, hTransverse⟩ :=
    hTargetFree.labelledStrictTree_glue Base D
      hTreeL hTreeR hcTL hcTR tL tR
      htL htR hLabelAgree
  have hWeakL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S)
      Target (jL ∘ fL) :=
    hL.postcomp_full jL
  have hWeakR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S)
      Target (jR ∘ fR) :=
    hR.postcomp_full jR
  have hRootMatch : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      (jL ∘ fL) ⟨sL d, hdL⟩ =
        (jR ∘ fR) ⟨sR d, hdR⟩ := by
    intro d hdL hdR
    change jL (fL ⟨sL d, hdL⟩) =
      jR (fR ⟨sR d, hdR⟩)
    rw [hRootL d hdL, hRootR d hdL hdR]
    exact (hTargetFree.overlap
      (aTL (q ⟨d, hdL⟩)) (aTR (q ⟨d, hdL⟩))).mpr
      ⟨q ⟨d, hdL⟩, rfl, rfl⟩
  obtain ⟨f, hWeak, hfLeft, hfRight⟩ :=
    hSrc.ambientRelativeWeakHE_glue S Target
      (jL ∘ fL) (jR ∘ fR)
      hWeakL hWeakR hRootMatch
  have hCopies : SetAmbientACopyIntersections A Whole Target S f :=
    hSrc.ambientACopyIntersections_glue hA S Target f
      (jL ∘ fL) (jR ∘ fR) hfLeft hfRight
      (hCopiesL.postcomp_full jL)
      (hCopiesR.postcomp_full jR)
  have hLabels : ∀ x : S, t (f x) = pWhole x.1 := by
    intro x
    rcases hSrc.covers x.1 with ⟨a, ha⟩ | ⟨b, hb⟩
    · have haS : iL a ∈ S := by
        rw [← ha]
        exact x.2
      have hEq : x = (⟨iL a, haS⟩ : S) := by
        apply Subtype.ext
        exact ha
      rw [hEq, hfLeft ⟨a, haS⟩]
      calc
        t (jL (fL ⟨a, haS⟩)) = tL (fL ⟨a, haS⟩) :=
          htLeft (fL ⟨a, haS⟩)
        _ = pL a := hfLabelsL ⟨a, haS⟩
        _ = pWhole (iL a) := (hpL a).symm
    · have hbS : iR b ∈ S := by
        rw [← hb]
        exact x.2
      have hEq : x = (⟨iR b, hbS⟩ : S) := by
        apply Subtype.ext
        exact hb
      rw [hEq, hfRight ⟨b, hbS⟩]
      calc
        t (jR (fR ⟨b, hbS⟩)) = tR (fR ⟨b, hbS⟩) :=
          htRight (fR ⟨b, hbS⟩)
        _ = pR b := hfLabelsR ⟨b, hbS⟩
        _ = pWhole (iR b) := (hpR b).symm
  have hHist : SetRespectsProjectedHistory pWhole S f history := by
    intro K _hK x y hxy
    have hPartEq : pWhole x.1 = pWhole y.1 := by
      calc
        pWhole x.1 = t (f x) := (hLabels x).symm
        _ = t (f y) := congrArg t hxy
        _ = pWhole y.1 := hLabels y
    rw [hPartEq]
  exact ⟨_, Target, hTree, t, ht, f, hWeak, hCopies,
    hLabels, hHist, hTransverse⟩

end StructuralRamsey.Structure.IsFreeAmalgam

import PartiteConstruction.Functional.OriginalPartialMarkedNoninjectiveRootGlue
import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Track D: closed mixed functional free cuts from the ORDINARY predecessor

English proof committed first in
docs/track-d-english-absolute-closed-mixed-ordinary-predecessor-20261112.md.

A strict functional predecessor on the exact CONTROL side images includes
genuine full A-copy intersection marks, without assuming protected marks.
Their *occupied* equations suffice to glue original-partial side maps
over a possibly COLLIDING source root, using the target-side mark theorem
of PR #635. Every side test is FULL, so ambient-relative weak HE on its
whole carrier upgrades to an original-2019 partial HE.

The result is an ABSOLUTE strict functional Base-tree completion.
It does NOT inherit projected-history/no-wrong-hit protection and
therefore is NOT the missing iterative HJ rank successor. The original
weak tested source vertices are never enlarged or closure-charged.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {E Y : Type v}

/-- Ambient-relative weak HE on the ENTIRE carrier becomes an
original-2019 partial HE of the actual full source structure, not just
its induced universal subtype. The change of carrier is a genuine
FULL structure embedding, not a weak or guessed quotient map. -/
theorem IsAmbientRelativeWeakHE.toOriginalPartialHE_univ
    {Side : Structure L E} {Target : Structure L Y}
    {f : (Set.univ : Set E) → Y}
    (h : IsAmbientRelativeWeakHE Side Set.univ Target f) :
    Side.IsOriginalPartialHomomorphismEmbedding Target
      (fun x : E => f ⟨x, Set.mem_univ x⟩) := by
  have hClosed : Side.IsClosed Set.univ := by
    intro F x _hx y _hy
    exact Set.mem_univ y
  have hInd : (Side.induce Set.univ hClosed).IsOriginalPartialHomomorphismEmbedding
      Target f :=
    h.toOriginalPartialHE_of_closed hClosed
  let e : Embedding Side (Side.induce Set.univ hClosed) := {
    toFun := fun x => ⟨x, Set.mem_univ x⟩
    injective := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R xs
      rfl
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨y.1, hy, Subtype.ext rfl⟩
  }
  exact hInd.comp e.isEHNHomomorphismEmbedding.toOriginalPartial

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA H E F Z VB P : Type v}

/-- Core mathematical improvement: the ORDINARY predecessor's exact
CONTROL image witnesses already produce compatible full TARGET A-marks
on a FULL mixed source free cut. No source-root injectivity or
closedness of either control image is required.

A new target mark is NOT assumed: it is extracted from each already
verified `SetAmbientACopyIntersections` predecessor certificate.
The source maps on each whole side are obtained by exact EHN pullback
and the univ-to-full-source original-partial conversion above.

The final theorem concerns ABSOLUTE strict B-tree completability only:
cross-side wrong target hits may destroy arbitrary projected histories.
-/
theorem originalPartialTreeCompletion_of_ordinaryControlSideImages
    {A : Structure L UA}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (pL : E → P) (pR : F → P)
    (hpL : Left.IsEHNHomomorphismEmbedding D pL)
    (hpR : Right.IsEHNHomomorphismEmbedding D pR)
    (hRootAgree : ∀ x : H, pL (sL x) = pR (sR x))
    (hRootInA : ∀ x : H, ∃ a : UA, pL (sL x) = alpha a)
    (Base : Structure L VB)
    (hControlL : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (pL '' (Set.univ : Set E)) [])
    (hControlR : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (pR '' (Set.univ : Set F)) []) :
    HasOriginalPartialTreeCompletion Base Whole := by
  classical
  obtain ⟨YL, TL, hTL, fL, hWeakL, hCopiesL, _hHistL⟩ := hControlL
  obtain ⟨YR, TR, hTR, fR, hWeakR, hCopiesR, _hHistR⟩ := hControlR
  obtain ⟨markL, hcMarkL, hMarkL⟩ := hCopiesL alpha
  obtain ⟨markR, hcMarkR, hMarkR⟩ := hCopiesR alpha
  let mapL : E → YL := fun x =>
    fL ⟨pL x, ⟨x, Set.mem_univ x, rfl⟩⟩
  let mapR : F → YR := fun x =>
    fR ⟨pR x, ⟨x, Set.mem_univ x, rfl⟩⟩
  have hPulledL : IsAmbientRelativeWeakHE Left Set.univ TL
      (fL ∘ (fun x : (Set.univ : Set E) =>
        (⟨pL x.1, ⟨x.1, x.2, rfl⟩⟩ :
          pL '' (Set.univ : Set E)))) :=
    hWeakL.pullback_ehn_exact hpL Set.univ fL
  have hPulledR : IsAmbientRelativeWeakHE Right Set.univ TR
      (fR ∘ (fun x : (Set.univ : Set F) =>
        (⟨pR x.1, ⟨x.1, x.2, rfl⟩⟩ :
          pR '' (Set.univ : Set F)))) :=
    hWeakR.pullback_ehn_exact hpR Set.univ fR
  have hPartialL : Left.IsOriginalPartialHomomorphismEmbedding TL mapL := by
    exact hPulledL.toOriginalPartialHE_univ
  have hPartialR : Right.IsOriginalPartialHomomorphismEmbedding TR mapR := by
    exact hPulledR.toOriginalPartialHE_univ
  let q : H → UA := fun x => Classical.choose (hRootInA x)
  have hQ (x : H) : pL (sL x) = alpha (q x) :=
    Classical.choose_spec (hRootInA x)
  have hRootL (x : H) : mapL (sL x) = markL (q x) := by
    have hmem : alpha (q x) ∈ pL '' (Set.univ : Set E) := by
      rw [← hQ x]
      exact ⟨sL x, Set.mem_univ _, rfl⟩
    calc
      mapL (sL x) = fL ⟨alpha (q x), hmem⟩ := by
        apply congrArg fL
        apply Subtype.ext
        exact hQ x
      _ = markL (q x) := (hMarkL (q x) hmem).symm
  have hRootR (x : H) : mapR (sR x) = markR (q x) := by
    have hEq : pR (sR x) = alpha (q x) :=
      (hRootAgree x).symm.trans (hQ x)
    have hmem : alpha (q x) ∈ pR '' (Set.univ : Set F) := by
      rw [← hEq]
      exact ⟨sR x, Set.mem_univ _, rfl⟩
    calc
      mapR (sR x) = fR ⟨alpha (q x), hmem⟩ := by
        apply congrArg fR
        apply Subtype.ext
        exact hEq
      _ = markR (q x) := (hMarkR (q x) hmem).symm
  exact hSrc.originalPartialTreeCompletion_of_marked_partialSides_noninjective
    Base TL TR hTL hTR markL markR hcMarkL hcMarkR q
    mapL mapR hPartialL hPartialR hRootL hRootR

/-- A true rank-m ORDINARY ambient-relative strict functional control
predecessor gives the two side-image marked witnesses AUTOMATICALLY
when their exact finite projected images each contain at most m parts.
No protected-mark predecessor or root-image domain-reflection premise.

The whole source can have arbitrary size or generator rank; obtaining
the side image budgets for a genuinely mixed exact (m+1)-vertex native
closed test is a separate exact finite-cardinality lemma.
-/
theorem originalPartialTreeCompletion_of_ordinaryControlRank
    {A : Structure L UA}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype E] [Fintype F] [DecidableEq P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (pL : E → P) (pR : F → P)
    (hpL : Left.IsEHNHomomorphismEmbedding D pL)
    (hpR : Right.IsEHNHomomorphismEmbedding D pR)
    (hRootAgree : ∀ x : H, pL (sL x) = pR (sR x))
    (hRootInA : ∀ x : H, ∃ a : UA, pL (sL x) = alpha a)
    (Base : Structure L VB)
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (hCardL : (Finset.univ.image pL).card ≤ m)
    (hCardR : (Finset.univ.image pR).card ≤ m) :
    HasOriginalPartialTreeCompletion Base Whole := by
  classical
  let IL : Finset P := Finset.univ.image pL
  let IR : Finset P := Finset.univ.image pR
  have hIL : (↑IL : Set P) = pL '' (Set.univ : Set E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, _hx, hxy⟩ := Finset.mem_image.mp hz
      exact ⟨x, Set.mem_univ _, hxy⟩
    · rintro ⟨x, _hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hIR : (↑IR : Set P) = pR '' (Set.univ : Set F) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, _hx, hxy⟩ := Finset.mem_image.mp hz
      exact ⟨x, Set.mem_univ _, hxy⟩
    · rintro ⟨x, _hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hControlL : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (pL '' (Set.univ : Set E)) [] := by
    simpa only [hIL] using hPrev IL hCardL []
  have hControlR : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (pR '' (Set.univ : Set F)) [] := by
    simpa only [hIR] using hPrev IR hCardR []
  exact hSrc.originalPartialTreeCompletion_of_ordinaryControlSideImages
    D alpha pL pR hpL hpR hRootAgree hRootInA Base
    hControlL hControlR

end StructuralRamsey.Structure.IsFreeAmalgam

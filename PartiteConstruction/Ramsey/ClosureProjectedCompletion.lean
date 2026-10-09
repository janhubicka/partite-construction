import PartiteConstruction.Ramsey.ClosureProjectedBoundary
import PartiteConstruction.Ramsey.ClosureClosedMapGlue

/-! # Mixed completion over a fixed closed projected boundary

This is stronger than the B-copywise boundary theorem. Given independent
K-completions of the two projected side sources and a common U-closed
K-member Q embedded in those sources, strong target amalgamation produces
a K-completion of the entire free source amalgam preserving every protected
closed test. The original source separator may be reducible and may be
collapsed by its map to Q.

No simultaneous-extension oracle is an input: the two completion maps
are chosen independently and their embeddings on Q are forced by the test
condition. The application to Lemma 2.30 still has to produce the displayed
source projections and prove the rank bounds on both projected sources.
This module uses the explicitly named closed-test working convention.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Construct a closed-test K-completion, not just a B-copywise map,
from independently completed projected sources sharing a fixed closed
irreducible member Q of K. Only the source amalgam is free. -/
theorem HasClosedUKCompletion.of_independent_projected_completions
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {V : Type v} (D : RelStructure L V), K D → D.Irreducible)
    {H E F C P X Y : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    [Finite P]
    (Q : RelStructure L P) (hQK : K Q) (hQClosed : IsUClosed rules Q)
    (DL : RelStructure L X) (DR : RelStructure L Y)
    (pL : E → X) (pR : F → Y)
    (hpL : IsClosedUHomomorphismEmbedding rules Left DL pL)
    (hpR : IsClosedUHomomorphismEmbedding rules Right DR pR)
    (q : H → P) (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hRootL : ∀ d, pL (sL d) = rL (q d))
    (hRootR : ∀ d, pR (sR d) = rR (q d))
    (hDL : HasClosedUKCompletion K rules DL)
    (hDR : HasClosedUKCompletion K rules DR) :
    HasClosedUKCompletion K rules Whole := by
  obtain ⟨XL, hXL, TL, hTL, _, fL, hfL⟩ := hDL
  obtain ⟨YR, hYR, TR, hTR, _, fR, hfR⟩ := hDR
  letI : Finite XL := hXL
  letI : Finite YR := hYR
  obtain ⟨eL, eR, heL, heR⟩ :=
    IsClosedUHomomorphismEmbedding.common_boundary_embeddings
      hQClosed (hKIrr Q hQK) rL rR hfL hfR
  obtain ⟨Z, hZ, Target, hTarget, jL, jR, hGlue, _⟩ :=
    hK Q TL TR hQK hTL hTR eL eR
  let gL : E → Z := jL ∘ (fL ∘ pL)
  let gR : F → Z := jR ∘ (fR ∘ pR)
  have hgL : IsClosedUHomomorphismEmbedding rules Left Target gL :=
    (jL.isClosedUHomomorphismEmbedding rules).comp (hfL.comp hpL)
  have hgR : IsClosedUHomomorphismEmbedding rules Right Target gR :=
    (jR.isClosedUHomomorphismEmbedding rules).comp (hfR.comp hpR)
  have hCompat : ∀ d, gL (sL d) = gR (sR d) := by
    intro d
    calc
      gL (sL d) = jL (fL (rL (q d))) := congrArg (fun x => jL (fL x)) (hRootL d)
      _ = jL (eL (q d)) := congrArg jL (heL (q d)).symm
      _ = jR (eR (q d)) := hGlue (q d)
      _ = jR (fR (rR (q d))) := congrArg jR (heR (q d))
      _ = gR (sR d) := congrArg (fun x => jR (fR x)) (hRootR d).symm
  exact ⟨Z, hZ, Target, hTarget, hKIrr Target hTarget,
    hSrc.compatibleFold gL gR hCompat,
    IsClosedUHomomorphismEmbedding.fold_free hSrc hRoot hLeft hRight
      gL gR hgL hgR hCompat⟩

end StructuralRamsey.RelStructure

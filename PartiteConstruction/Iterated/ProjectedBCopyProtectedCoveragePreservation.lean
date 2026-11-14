import PartiteConstruction.Iterated.ProjectedBCopyClosedHullAttachment
import PartiteConstruction.Ramsey.ClosureClosedMapGlue
import PartiteConstruction.Ramsey.ClosureSemiClosed2019

/-!
# Track E: protected external B-coverage survives closed-root B attachments

The corrected 2019 two-pass target carries an EXTERNAL test-coverage
invariant: every U-closed, U-irreducible embedded source test embeds
fully into the canonical Base. This invariant is exactly stable under
free amalgamation over an intrinsically U-CLOSED root, provided both
sides have such external coverage.

The proof does NOT assert an internal B-copy extension for every test:
that stronger assertion requires an additional finite attachment pass.
It also does NOT assert arbitrary weak-test H-completion preservation.
Those properties have different quantifier contracts.

For the U-closed closed-hull B attachment in the preceding Track E
module, the old side has protected B coverage by hypothesis and the
right side is itself Base, so all protected tests of the new source
still embed in Base. This enables an induction over repeated closed
attachments without losing the external invariant.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C B : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E}
variable {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {Base : RelStructure L B}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Exact external B-coverage is inherited by the free amalgam from
its two sides, when the literal common root is U-closed. No cardinal
budget, source hull substitution or original map is changed. -/
theorem freeAmalgam_preserves_externalBCoverage
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (hCoverLeft : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Left → Nonempty (Embedding Test Base))
    (hCoverRight : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Right → Nonempty (Embedding Test Base)) :
    ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Whole → Nonempty (Embedding Test Base) := by
  intro X Test hTestClosed hTestIrred e
  rcases hFree.closed_test_factor hRoot
      hLeft.isUSemiClosed hRight.isUSemiClosed
      Test hTestClosed hTestIrred e with ⟨gL, _⟩ | ⟨gR, _⟩
  · exact hCoverLeft Test hTestClosed hTestIrred gL
  · exact hCoverRight Test hTestClosed hTestIrred gR

/-- If the right free side embeds fully in Base, every protected
test on that side embeds in Base by composition. In particular the
closed-root attachment with Right = Base uses its identity embedding.
This retains the exact external B-protection of the old core. -/
theorem freeAmalgam_rightEmbeddedInBase_preserves_externalBCoverage
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (eRight : Embedding Right Base)
    (hCoverLeft : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Left → Nonempty (Embedding Test Base)) :
    ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Whole → Nonempty (Embedding Test Base) := by
  have hCoverRight : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Right → Nonempty (Embedding Test Base) := by
    intro X Test _ _ e
    exact ⟨eRight.comp e⟩
  exact freeAmalgam_preserves_externalBCoverage
    hFree hRoot hLeft hRight hCoverLeft hCoverRight


/-- The repaired projected B attachment over the exact closed hull
retains all THREE relevant one-step certificates simultaneously:
U-CLOSEDNESS of the new source, its selected CONTROL HE, and external
B-coverage for EVERY U-closed U-irreducible new source test. The core's
old selected projection agrees exactly on all original vertices.

The whole construction remains RELATIONAL. This result does not prove
relative small-H test completion preservation or normality of an
arbitrary genuinely partial whole-mask target after attachment. -/
theorem attach_closedHull_preserves_all_three
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hOrigClosed : IsUClosed rules Orig)
    (hBaseClosed : IsUClosed rules Base)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control)
    (S : Set O) (hSIrred : (Orig.induce S).Irreducible) :
    ∃ (H : Set O), S ⊆ H ∧
      ∃ (j : Embedding (Orig.induce H) Base)
        (newProjection :
          FreeAmalgam.Vertex (Orig.induce H) Orig Base
            (inclusion Orig H) j → Q),
        IsUClosed rules
          (FreeAmalgam.amalgam (Orig.induce H) Orig Base
            (inclusion Orig H) j) ∧
        (FreeAmalgam.amalgam (Orig.induce H) Orig Base
          (inclusion Orig H) j).IsHomomorphismEmbedding
          Control newProjection ∧
        (∀ o : O, newProjection
          (FreeAmalgam.leftEmbedding
            (Orig.induce H) Orig Base (inclusion Orig H) j o) =
            pOrig o) ∧
        (∀ {X : Type v} (Test : RelStructure L X),
          IsUClosed rules Test → IsUIrreducible rules Test →
          Embedding Test
            (FreeAmalgam.amalgam (Orig.induce H) Orig Base
              (inclusion Orig H) j) →
          Nonempty (Embedding Test Base)) := by
  classical
  obtain ⟨H, hSH, hHClosed, _hHUIrred, hHOrdIrred, beta, hBeta⟩ :=
    closedHull_has_selected_controlBCopy
      Orig Base Control pOrig hOrigClosed hExternal
      hBaseHered hpOrig hControl S hSIrred
  let i : Embedding (Orig.induce H) Orig := inclusion Orig H
  obtain ⟨j, newProjection, hProjected, hLeft, _hRight, _hOverlap⟩ :=
    attach_irreducible_preserves_controlHE
      hHOrdIrred i pOrig hpOrig beta hBeta
  have hFree : IsFreeAmalgam i j
      (FreeAmalgam.leftEmbedding (Orig.induce H) Orig Base i j)
      (FreeAmalgam.rightEmbedding (Orig.induce H) Orig Base i j) :=
    FreeAmalgam.isFreeAmalgam (Orig.induce H) Orig Base i j
  have hWholeClosed :
      IsUClosed rules
        (FreeAmalgam.amalgam (Orig.induce H) Orig Base i j) :=
    hFree.isUClosed hHClosed hOrigClosed hBaseClosed
  have hWholeExternal :
      ∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test
          (FreeAmalgam.amalgam (Orig.induce H) Orig Base i j) →
        Nonempty (Embedding Test Base) :=
    freeAmalgam_rightEmbeddedInBase_preserves_externalBCoverage
      hFree hHClosed hOrigClosed hBaseClosed (Embedding.id Base) hExternal
  exact ⟨H, hSH, j, newProjection,
    hWholeClosed, hProjected, hLeft, hWholeExternal⟩

end StructuralRamsey.RelStructure.ProjectedBCopyControl

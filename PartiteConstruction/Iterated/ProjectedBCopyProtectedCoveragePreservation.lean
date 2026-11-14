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

/-- If the right free side IS Base, every protected test on that side
embeds into Base by the identity. The closed-root attachment thus
retains the exact external B-protection of the entire old core. -/
theorem freeAmalgam_attachBase_preserves_externalBCoverage
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (BaseEq : Right = Base)
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
    cases BaseEq
    exact ⟨e⟩
  exact freeAmalgam_preserves_externalBCoverage
    hFree hRoot hLeft hRight hCoverLeft hCoverRight

end StructuralRamsey.RelStructure.ProjectedBCopyControl

import PartiteConstruction.Functional.WeakBareFullAttachmentControlBudget
import PartiteConstruction.Functional.EHNAttachmentDecompose

/-!
# Track D: bare strict functional rank successor for ACTUAL UnitAttachD

English proof committed FIRST:
docs/track-d-english-native-unit-bare-control-budget-20261114.md.

The checked functional partite attachment is a TRUE full native
source free amalgam over its ACTUAL function-closed selected
support, preserving genuine EHN projection and transverse
set-valued output fibres. Its common root projects inside
the selected FULL A↪D, without source-root injectivity.

Invoke the generic BARE rank successor from draft #683.
No weak source test or projected side image is closed; the
extra control rank F_A(m) is explicitly assumed and NOT
silently inferred from rank m.

This proves one genuine binary native stage conditionally.
Finite HJ list integration, a NONCIRCULAR outer budget
schedule, the final original-2019 arrow and B-coverage
remain separate obligations.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The actual native full FUNCTIONAL one-copy selected-support
attachment inherits the bare strict B-tree exact weak
rank m+1 from BOTH full source sides, provided the
FIXED EHN control D has paid finite A-trace budget F_A(m).

No common HJ parameter coordinate is needed: the result
concerns EVERY actual full selected-support attachment
embedding f, including those arising from different
Hales–Jewett lines. Control rank inflation is a real
hypothesis, not a source weak-test rank inflation. -/
theorem UnitAttachD_bareRank_of_controlBudget
    [Finite P] [Fintype U] [Finite V] [Finite W]
    (Old : System L P V) (D : Structure L P)
    (hOld : Old.WeaklyPartiteOver D)
    (A : Structure L U) (hA : A.Irreducible)
    (alpha : Structure.Embedding A D)
    (Core : System L P W)
    (hCore : Core.WeaklyPartiteOver D)
    (f : FunctionalPartite.Embedding
      (Old.induce (Old.support alpha.toFunctionEmbedding)
        (Old.weak_support_closed D hOld.1 A alpha)) Core)
    (Base : Structure L VB) (m : ℕ)
    (hBareCore :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base Core.toStructure (m + 1))
    (hBareOld :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base Old.toStructure (m + 1))
    (hBareControl :
      SetAmbientRelativeWeakTreeWitness.AtMostBare Base D
        (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := U) m)) :
    let S := Old.support alpha.toFunctionEmbedding
    let hS := Old.weak_support_closed D hOld.1 A alpha
    SetAmbientRelativeWeakTreeWitness.AtMostBare
      Base (UnitAttachD Old S hS Core f).toStructure (m + 1) := by
  classical
  letI : Fintype P := Fintype.ofFinite _
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  let S := Old.support alpha.toFunctionEmbedding
  let hS := Old.weak_support_closed D hOld.1 A alpha
  let Whole := UnitAttachD Old S hS Core f
  let cEmb : FunctionalPartite.Embedding Core Whole :=
    FunctionalPartite.Attachment.coreEmbedding
      Old S hS Core (fun _ : PUnit.{v+1} => f)
  have hp : Whole.toStructure.IsEHNHomomorphismEmbedding
      D Whole.part :=
    FunctionalPartite.Attachment.unit_weaklyPartiteOver
      Old S hS Core f D hOld hCore
  have hFree : IsFreeAmalgam
      f.toEmbedding
      (Structure.inclusion Old.toStructure S hS)
      (unitCoreEmbedding Old S hS Core f)
      (unitCopyEmbedding Old S hS Core f) :=
    unit_isFreeAmalgam_full Old S hS Core f
  let R := Old.weakRestrict D hOld.1 A alpha
  have hRootAlpha : ∀ x : S,
      ∃ a : U,
        Whole.part ((unitCoreEmbedding Old S hS Core f) (f x)) =
          alpha a := by
    intro x
    refine ⟨R.part x, ?_⟩
    calc
      Whole.part ((unitCoreEmbedding Old S hS Core f) (f x)) =
          Whole.part (cEmb (f x)) := rfl
      _ = Core.part (f x) := cEmb.map_part (f x)
      _ = Old.part x.1 := f.map_part x
      _ = alpha (R.part x) :=
        (Old.restrictedPart_spec alpha.toFunctionEmbedding x).symm
  exact hFree.AtMostBare_of_control_budget_mixed_full_cut
    hA D alpha Whole.part hp hRootAlpha
    Base m hBareCore hBareOld hBareControl

end StructuralRamsey.FunctionalPartite.Attachment

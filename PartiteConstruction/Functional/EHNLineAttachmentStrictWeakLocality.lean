import PartiteConstruction.Functional.EHNLineAttachmentRetraction
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Actual one-line functional HJ attachment preserves strict weak-tree locality

The real native EHN Picture attaches a genuine full copied OLD Picture
along a FULL Hales–Jewett line of its selected function-closed support.

The previously proved line-specific EHN retraction evaluates a chosen
parameter coordinate on the genuine HJ power core and acts as ID on
the copied OLD Picture. It also COMMUTES WITH THE ORIGINAL CONTROL
PART PROJECTION. Thus for every exact weak vertex test S in the
attached system, its retraction image q[S] in OLD has cardinality
at most |S|. The strict B-tree completion of q[S] transfers through
the full functional EHN shadow to S.

Hence a SINGLE actual HJ line attachment preserves at the SAME n:
* strict FULL-FUNCTIONAL Base-tree witnesses on all exact weak tests,
* ambient-relative weak HEs for genuinely SET-VALUED functions,
* full protection of ACTUAL ambient A-copy intersections,
* all finite projected-history diaries of the ORIGINAL control,
* the original-2019 partial HE conclusion on genuinely closed tests.

The function-output fibres of the resulting partite System are
TRANSVERSAL by the already verified functional attachment invariant.

This does NOT claim preservation through an arbitrary LIST of line
attachments: different lines need not have one common EHN retraction
onto OLD. Such multi-line coherence remains the actual hard
maximal mixed partite induction problem.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V U UA VB : Type v}

/-- The actual SINGLE native functional Hales-Jewett line attachment
preserves the strict functional n-vertex weak-history invariant,
assuming OLD has it.

The selected support is genuinely CLOSED only for constructing the
full source attachment; all tested local vertex sets remain arbitrary
exact WEAK subsets without function-closure enlargement. The output
structure carries all set-valued functions and transversal images. -/
theorem lineUnitAttachment_preserves_strictWeakHistoryAtMost
    [DecidableEq V]
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U) (alpha : Structure.Embedding A D)
    (N : ℕ)
    (W : Line (Induced.Letter A
      (B.weakRestrict D hB.1 A alpha)) N)
    (i : Fin N) (hi : W.symbol i = .parameter)
    (TestA : Structure L UA) (Base : Structure L VB)
    (hTestA : TestA.Irreducible)
    (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMost
      TestA Base B.toStructure B.part n) :
    let S : Set V := B.support alpha.toFunctionEmbedding
    let hS : B.toStructure.IsClosed S :=
      B.weak_support_closed D hB.1 A alpha
    let R := B.weakRestrict D hB.1 A alpha
    let E := Induced.power R N
    let Core := E.relabel alpha.toFunctionEmbedding
    ∃ f : FunctionalPartite.Embedding (B.induce S hS) Core,
      SetAmbientRelativeWeakTreeWitness.AtMost
        TestA Base
        (Attachment.UnitAttachD B S hS Core f).toStructure
        (Attachment.UnitAttachD B S hS Core f).part n := by
  classical
  dsimp only
  let S : Set V := B.support alpha.toFunctionEmbedding
  let hS : B.toStructure.IsClosed S :=
    B.weak_support_closed D hB.1 A alpha
  let R := B.weakRestrict D hB.1 A alpha
  let E := Induced.power R N
  let Core := E.relabel alpha.toFunctionEmbedding
  obtain ⟨f, q, hq, _hqCore, _hqCopy, hPart⟩ :=
    lineUnitAttachment_EHN_retraction B D hB A alpha N W i hi
  refine ⟨f, ?_⟩
  exact SetAmbientRelativeWeakTreeWitness.AtMost.pullback_ehn_commutingParts
    (Attachment.UnitAttachD B S hS Core f).part
    B.part q hq (fun z => (hPart z).symm)
    hTestA n hOld

end StructuralRamsey.FunctionalPartite.EHN

import PartiteConstruction.Functional.EHNLineAttachmentRetraction
import PartiteConstruction.Functional.WeakHistoryFreeSmallImagePullback

/-!
# Track D: a single actual HJ line inherits no-history strict weak locality

English proof written before Lean:
docs/track-d-english-single-hj-line-historyfree-inheritance-20261113.md

A genuine ONE-LINE native full-functional attachment retracts by the
verified HJ parameter-coordinate EHN map onto the entire copied Old
picture, fixing that copy pointwise. The checked exact-image
AtMostNoHistory.pullback_ehn preserves EVERY weak finite test, all
genuine ambient full irreducible A-copy intersections and the strict
functional B-tree witness at the SAME vertex rank, regardless of
colliding source roots or source-undefined function domains.

This is only one HJ line: distinct lines may not share a parameter
coordinate, so no common EHN retraction is inferred for their union.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P U V VB : Type v}

/-- A FULL native attachment along ONE actual Hales--Jewett line
preserves the no-history strict original-function-language
ambient-relative weak-tree invariant on exactly every tested set.

The old-stage A need only be irreducible; no global injection of
the EHN retraction and no closure of the weak tested subset is used.
No multi-line history or arbitrary projected-history diary is claimed. -/
theorem lineUnitAttachment_preserves_noHistoryAtMost
    [DecidableEq V]
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U) (alpha : Structure.Embedding A D)
    (N : ℕ)
    (W : Line (Induced.Letter A
      (B.weakRestrict D hB.1 A alpha)) N)
    (i : Fin N) (hi : W.symbol i = .parameter)
    (TestA : Structure L U) (Base : Structure L VB)
    (hTestA : TestA.Irreducible)
    (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMostNoHistory
      TestA Base B.toStructure B.part n) :
    let S : Set V := B.support alpha.toFunctionEmbedding
    let hS : B.toStructure.IsClosed S :=
      B.weak_support_closed D hB.1 A alpha
    let R := B.weakRestrict D hB.1 A alpha
    let E := Induced.power R N
    let Core := E.relabel alpha.toFunctionEmbedding
    ∃ f : FunctionalPartite.Embedding (B.induce S hS) Core,
      SetAmbientRelativeWeakTreeWitness.AtMostNoHistory
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
  obtain ⟨f, q, hq, _hqCore, _hqCopy, _hPart⟩ :=
    lineUnitAttachment_EHN_retraction B D hB A alpha N W i hi
  refine ⟨f, ?_⟩
  exact SetAmbientRelativeWeakTreeWitness.AtMostNoHistory.pullback_ehn
    hTestA q hq
    (Attachment.UnitAttachD B S hS Core f).part B.part
    n hOld

end StructuralRamsey.FunctionalPartite.EHN

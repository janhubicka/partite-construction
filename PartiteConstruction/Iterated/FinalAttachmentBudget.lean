import PartiteConstruction.Iterated.FinalAttachment
import PartiteConstruction.Iterated.RootedWitness

/-! # Final attachment with an explicit root budget

Only the control structure and the whole gluing root are required to be
irreducible.  No hereditary irreducibility assumption is made on either of
them, or on the base structure.  Testing the old-side vertices together with
the entire root costs at most |root| extra vertices.  The two target witnesses
are glued over the whole root, not over its possibly reducible intersection
with the original test set.

Ambient control is inherited directly from the rooted old-side witness and
the fresh base copy, using localization of irreducibles in a free amalgam.
The stronger completeControl lemma is not used.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H X : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {D : RelStructure L H} {Core : RelStructure L X}
variable {fCore : Embedding D Core} {fBase : Embedding D Base}

/-- A final free attachment over an arbitrary irreducible root, with the
explicit loss of at most |root| in the local-tree size bound. -/
theorem freeAmalgam_rootBudget
    [Finite UA] [Finite VB] [Finite H] [Finite X]
    (hControl : Control.Irreducible)
    (hD : D.Irreducible) (n : ℕ)
    (hCore : LocallyTreeLike Control Base Core (n + Nat.card H)) :
    LocallyTreeLike Control Base
      (FreeAmalgam.amalgam D Core Base fCore fBase) n := by
  classical
  intro S hScard
  let Support := FreeAmalgam.support D Core Base fCore fBase
  let g : Unit → Embedding (Base.induce Support) Core :=
    fun _ => FreeAmalgam.overlapEmbedding D Core Base fCore fBase
  let Whole := FreeAmalgam.amalgam D Core Base fCore fBase
  let Tset : Set (FreeAmalgam.Vertex D Core Base fCore fBase) := ↑S
  let Small := Whole.induce Tset
  let smallIncl : Embedding Small Whole := inclusion Whole Tset

  let Piece := Attachment.Piece Base Support Core g Tset ()
  let Rest := Attachment.Rest Base Support Core g Tset ()
  let Overlap := Attachment.Overlap Base Support Core g Tset ()
  let PieceV := Attachment.PieceV Base Support Core g Tset ()
  let RestV := Attachment.RestV (W := X) (I := Unit) Support Tset ()
  let OverlapV := Attachment.OverlapV Base Support Core g Tset ()
  let sPiece := Attachment.overlapToPiece Base Support Core g Tset ()
  let sRest := Attachment.overlapToRest Base Support Core g Tset ()
  let iPiece := Attachment.pieceInclusion Base Support Core g Tset ()
  let iRest := Attachment.restInclusion Base Support Core g Tset ()
  have hFree : IsFreeAmalgam sPiece sRest iPiece iRest :=
    Attachment.decompose Base Support Core g Tset ()

  let l := FreeAmalgam.leftEmbedding D Core Base fCore fBase
  let r := FreeAmalgam.rightEmbedding D Core Base fCore fBase
  let ePieceWhole : Embedding Piece Whole := smallIncl.comp iPiece
  let eRestWhole : Embedding Rest Whole := smallIncl.comp iRest
  have hPieceRange : ∀ z : PieceV, ∃ b : VB, ePieceWhole z = r b := by
    intro z
    rcases z.2 with ⟨b, hb⟩
    exact ⟨b, hb⟩
  have hRestRange : ∀ z : RestV, ∃ x : X, eRestWhole z = l x := by
    intro z
    cases hz : z.1.1 with
    | inl x => exact ⟨x, hz⟩
    | inr pair =>
        rcases pair with ⟨i, b⟩
        have hi : i = () := Subsingleton.elim _ _
        subst i
        exact (z.2 ⟨b, hz⟩).elim
  let ePiece : Embedding Piece Base :=
    ePieceWhole.factorThroughRange r hPieceRange
  let eRest : Embedding Rest Core :=
    eRestWhole.factorThroughRange l hRestRange
  have hPieceSpec (z : PieceV) : ePieceWhole z = r (ePiece z) :=
    Classical.choose_spec (hPieceRange z)
  have hRestSpec (z : RestV) : eRestWhole z = l (eRest z) :=
    Classical.choose_spec (hRestRange z)

  have hOverlapRange : ∀ z : OverlapV, ∃ d : H,
      eRest (sRest z) = fCore d ∧ ePiece (sPiece z) = fBase d := by
    intro z
    have hsmall : iPiece (sPiece z) = iRest (sRest z) :=
      (hFree.overlap (sPiece z) (sRest z)).mpr ⟨z, rfl, rfl⟩
    have hwhole : l (eRest (sRest z)) = r (ePiece (sPiece z)) := by
      calc
        l (eRest (sRest z)) = eRestWhole (sRest z) :=
          (hRestSpec (sRest z)).symm
        _ = ePieceWhole (sPiece z) := congrArg smallIncl hsmall.symm
        _ = r (ePiece (sPiece z)) := hPieceSpec (sPiece z)
    exact ((FreeAmalgam.isFreeAmalgam D Core Base fCore fBase).overlap
      (eRest (sRest z)) (ePiece (sPiece z))).mp hwhole
  let q : OverlapV → H := fun z => Classical.choose (hOverlapRange z)

  letI : Fintype Tset := Fintype.ofFinite Tset
  letI : Fintype RestV := Fintype.ofFinite RestV
  have hRestCard : Nat.card RestV ≤ n := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card RestV ≤ Fintype.card Tset :=
        Fintype.card_le_of_injective (fun z : RestV => z.1)
          (by intro a b hab; exact Subtype.ext hab)
      _ ≤ n := by simpa [Tset] using hScard
  obtain ⟨YR, TR, hTreeR, pRest, hpRest, tRoot, htRoot, ctrlRest⟩ :=
    rootedWitness_controlled hD fCore eRest n hRestCard hCore

  let pPiece : PieceV → VB := ePiece
  have hpPiece : Piece.IsHomomorphismEmbedding Base pPiece :=
    ePiece.isHomomorphismEmbedding
  have hcompatPiece : ∀ z, pPiece (sPiece z) = fBase (q z) := by
    intro z
    exact (Classical.choose_spec (hOverlapRange z)).2
  have hcompatRest : ∀ z, pRest (sRest z) = tRoot (q z) := by
    intro z
    exact htRoot (sRest z) (q z) (Classical.choose_spec (hOverlapRange z)).1

  let Target := FreeAmalgam.amalgam D Base TR fBase tRoot
  let jPiece := FreeAmalgam.leftEmbedding D Base TR fBase tRoot
  let jRest := FreeAmalgam.rightEmbedding D Base TR fBase tRoot
  have hcPiece : fBase.ContainedInIrreducible := by
    exact ⟨Set.range fBase, hD.range_embedding fBase, fun d => ⟨d, rfl⟩⟩
  have hcRest : tRoot.ContainedInIrreducible := by
    exact ⟨Set.range tRoot, hD.range_embedding tRoot, fun d => ⟨d, rfl⟩⟩
  have hTree : TreeAmalgam Base
      (FreeAmalgam.Vertex D Base TR fBase tRoot) Target :=
    FreeAmalgam.treeAmalgam D Base TR fBase tRoot Base
      (TreeAmalgam.copy (Iso.refl Base)) hTreeR hcPiece hcRest
  have hTgt : IsFreeAmalgam fBase tRoot jPiece jRest :=
    FreeAmalgam.isFreeAmalgam D Base TR fBase tRoot
  let pSmall : Tset → FreeAmalgam.Vertex D Base TR fBase tRoot :=
    IsFreeAmalgam.liftMap hFree hTgt q pPiece pRest hcompatPiece hcompatRest
  have hpSmall : Small.IsHomomorphismEmbedding Target pSmall :=
    IsFreeAmalgam.liftMap_isHomomorphismEmbedding
      hFree hTgt q pPiece pRest hcompatPiece hcompatRest hpPiece hpRest
  refine ⟨FreeAmalgam.Vertex D Base TR fBase tRoot, Target, hTree,
    pSmall, hpSmall, ?_⟩
  intro α
  have hWholeFree := FreeAmalgam.isFreeAmalgam D Core Base fCore fBase
  rcases hWholeFree.irreducible_side (Set.range α)
      (hControl.range_embedding α) with hleft | hright
  · have hrange : ∀ a : UA, ∃ x : X, α a = l x := by
      intro a
      exact hleft ⟨α a, ⟨a, rfl⟩⟩
    let αCore : Embedding Control Core := α.factorThroughRange l hrange
    have hαCore (a : UA) : α a = l (αCore a) :=
      Classical.choose_spec (hrange a)
    obtain ⟨αT, hαT⟩ := ctrlRest αCore
    refine ⟨jRest.comp αT, ?_⟩
    intro a ha
    let z : Tset := ⟨α a, ha⟩
    have hzRest : ¬ Attachment.OutsideAt (S := Support) () z.1 := by
      rintro ⟨b, hb⟩
      have hbad : (Sum.inl (αCore a) :
          FreeAmalgam.Vertex D Core Base fCore fBase) = Sum.inr ((), b) :=
        (hαCore a).symm.trans hb
      cases hbad
    let zr : RestV := ⟨z, hzRest⟩
    have heq : eRest zr = αCore a := by
      apply l.injective
      calc
        l (eRest zr) = eRestWhole zr := (hRestSpec zr).symm
        _ = α a := rfl
        _ = l (αCore a) := hαCore a
    obtain ⟨a', ha'⟩ := hαT zr a heq
    refine ⟨a', ?_⟩
    change pSmall z = jRest (αT a')
    calc
      pSmall z = jRest (pRest zr) :=
        IsFreeAmalgam.liftMap_right hFree hTgt q pPiece pRest
          hcompatPiece hcompatRest zr
      _ = jRest (αT a') := congrArg jRest ha'
  · have hrange : ∀ a : UA, ∃ b : VB, α a = r b := by
      intro a
      exact hright ⟨α a, ⟨a, rfl⟩⟩
    let αBase : Embedding Control Base := α.factorThroughRange r hrange
    have hαBase (a : UA) : α a = r (αBase a) :=
      Classical.choose_spec (hrange a)
    refine ⟨jPiece.comp αBase, ?_⟩
    intro a ha
    let z : Tset := ⟨α a, ha⟩
    let zp : PieceV := ⟨z, ⟨αBase a, hαBase a⟩⟩
    have heq : ePiece zp = αBase a := by
      apply r.injective
      calc
        r (ePiece zp) = ePieceWhole zp := (hPieceSpec zp).symm
        _ = α a := rfl
        _ = r (αBase a) := hαBase a
    refine ⟨a, ?_⟩
    change pSmall z = jPiece (αBase a)
    calc
      pSmall z = jPiece (pPiece zp) :=
        IsFreeAmalgam.liftMap_left hFree hTgt q pPiece pRest
          hcompatPiece hcompatRest zp
      _ = jPiece (αBase a) := congrArg jPiece heq

end StructuralRamsey.RelStructure.LocallyTreeLike

namespace StructuralRamsey.RelStructure.FreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H X Y : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {D : RelStructure L H} {Core : RelStructure L X}
variable {Q : RelStructure L Y} {fCore : Embedding D Core}

/-- Both final-attachment invariants, with an explicit root-size budget and
no hereditary irreducibility hypothesis or auxiliary Control-to-Base embedding. -/
theorem attachOverIrreducible_preservesProjectionAndLocalTree_rootBudget
    [Finite UA] [Finite VB] [Finite H] [Finite X]
    (hControl : Control.Irreducible)
    (hD : D.Irreducible) (n : ℕ)
    (hCoreLTL : LocallyTreeLike Control Base Core (n + Nat.card H))
    (pCore : X → Y) (hpCore : Core.IsHomomorphismEmbedding Q pCore)
    (β : Embedding Base Q)
    (hcover : ∀ d : H, ∃ b : VB, pCore (fCore d) = β b) :
    ∃ fBase : Embedding D Base,
      ∃ p : Vertex D Core Base fCore fBase → Y,
        (amalgam D Core Base fCore fBase).IsHomomorphismEmbedding Q p ∧
        LocallyTreeLike Control Base (amalgam D Core Base fCore fBase) n ∧
        (∀ x : X, p (leftEmbedding D Core Base fCore fBase x) = pCore x) ∧
        ∀ b : VB, p (rightEmbedding D Core Base fCore fBase b) = β b := by
  obtain ⟨fBase, p, hp, hleft, hright⟩ :=
    attachOverIrreducible_preservesProjection
      (D := D) (A := Core) (B := Base) (Q := Q) (fA := fCore)
      hD pCore hpCore β hcover
  have hLocal : LocallyTreeLike Control Base
      (amalgam D Core Base fCore fBase) n :=
    LocallyTreeLike.freeAmalgam_rootBudget hControl hD n hCoreLTL
  exact ⟨fBase, p, hp, hLocal, hleft, hright⟩

end StructuralRamsey.RelStructure.FreeAmalgam

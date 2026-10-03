import PartiteConstruction.Iterated.FinalAttachment
import PartiteConstruction.Iterated.RootedWitness

/-! # Final attachment with an explicit root budget

The previous same-level attachment theorem assumes hereditary irreducibility
of the root.  Here only the root itself is irreducible.  Local tree-likeness
of the old core at level n + |root| suffices at level n after attachment.

The proof includes the whole root in the old-side test set, then glues the
two target witnesses over that whole root.  The source overlap need not be
irreducible and need not equal the target overlap.  Control of ambient A-copies
is restored by the existing completeControl theorem; its hereditary hypothesis
on A is still explicit and is not discharged here.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H X : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {D : RelStructure L H} {Core : RelStructure L X}
variable {fCore : Embedding D Core} {fBase : Embedding D Base}

/-- Include the entire irreducible root in the old-side test set before
forming the target free amalgam.  No hereditary hypothesis on D or Base is
required. -/
theorem freeAmalgam_rootBudget
    [Finite UA] [Finite VB] [Finite H] [Finite X]
    (hControl : HereditarilyIrreducible Control)
    (eControlBase : Embedding Control Base)
    (hD : D.Irreducible)
    (n : ℕ)
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
  have hPieceSpec (z : PieceV) : ePieceWhole z = r (ePiece z) := by
    exact Classical.choose_spec (hPieceRange z)
  have hRestSpec (z : RestV) : eRestWhole z = l (eRest z) := by
    exact Classical.choose_spec (hRestRange z)

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
  obtain ⟨YR, TR, hTreeR, pRest, hpRest, tRoot, htRoot⟩ :=
    rootedWitness hD fCore eRest n hRestCard hCore

  let pPiece : PieceV → VB := ePiece
  have hpPiece : Piece.IsHomomorphismEmbedding Base pPiece :=
    ePiece.isHomomorphismEmbedding
  have ctrlPiece : ∀ α : Embedding Control Piece,
      ∃ α' : Embedding Control Base,
        ∀ a : UA, ∃ a' : UA, pPiece (α a) = α' a' := by
    intro α
    exact ⟨ePiece.comp α, fun a => ⟨a, rfl⟩⟩
  have ctrlRest : ∀ α : Embedding Control Rest,
      ∃ α' : Embedding Control TR,
        ∀ a : UA, ∃ a' : UA, pRest (α a) = α' a' := by
    intro α
    obtain ⟨α', hα'⟩ := hpRest.after_irreducible_embedding hControl.irreducible α
    exact ⟨α', fun a => ⟨a, (hα' a).symm⟩⟩
  have hcompatPiece : ∀ z, pPiece (sPiece z) = fBase (q z) := by
    intro z
    exact (Classical.choose_spec (hOverlapRange z)).2
  have hcompatRest : ∀ z, pRest (sRest z) = tRoot (q z) := by
    intro z
    exact htRoot (sRest z) (q z) (Classical.choose_spec (hOverlapRange z)).1

  obtain ⟨Y, T, hTree, pSmall, hpSmall, _⟩ :=
    glueControlled (tE := fBase) (tF := tRoot)
      hControl.irreducible hFree hD
      (TreeAmalgam.copy (Iso.refl Base)) hTreeR
      q pPiece pRest hcompatPiece hcompatRest
      hpPiece hpRest ctrlPiece ctrlRest
  have hpSmall' :
      (Whole.induce (↑S : Set _)).IsHomomorphismEmbedding T pSmall := by
    simpa [Small, Tset, Whole, g, Support, FreeAmalgam.amalgam] using hpSmall
  exact completeControl (A := Control) (B := Base) (C := Whole)
    hControl eControlBase S hTree pSmall hpSmall'

end StructuralRamsey.RelStructure.LocallyTreeLike

namespace StructuralRamsey.RelStructure.FreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H X Y : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {D : RelStructure L H} {Core : RelStructure L X}
variable {Q : RelStructure L Y} {fCore : Embedding D Core}

/-- Final attachment with both projection and local-tree guarantees, using
an explicit root-size budget instead of hereditary irreducibility of Base. -/
theorem attachOverIrreducible_preservesProjectionAndLocalTree_rootBudget
    [Finite UA] [Finite VB] [Finite H] [Finite X]
    (hControl : HereditarilyIrreducible Control)
    (eControlBase : Embedding Control Base)
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
    LocallyTreeLike.freeAmalgam_rootBudget
      hControl eControlBase hD n hCoreLTL
  exact ⟨fBase, p, hp, hLocal, hleft, hright⟩

end StructuralRamsey.RelStructure.FreeAmalgam

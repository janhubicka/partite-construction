import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Iterated.WitnessGlue
import PartiteConstruction.Iterated.ControlCompletion

/-! # Projection through a final free attachment

The final sparsening step attaches a copy of `B` over an irreducible
substructure while keeping a homomorphism-embedding into the original Ramsey
witness.  This file supplies the reusable one-step projection lemma.

Two homomorphism-embeddings of the sides of a concrete free amalgam can be
folded to a common target whenever they agree on the overlap.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Hereditary irreducibility pulls back along induced embeddings. -/
theorem HereditarilyIrreducible.pullback
    {U V : Type v} {A : RelStructure L U} {B : RelStructure L V}
    (hB : HereditarilyIrreducible B) (e : Embedding A B) :
    HereditarilyIrreducible A := by
  intro S
  exact hB.of_embedding (e.comp (inclusion A S))

namespace LocallyTreeLike

/-- The base structure itself is locally tree-like over one copy of itself. -/
theorem base
    {U V : Type v} (A : RelStructure L U) (B : RelStructure L V)
    (n : ℕ) :
    LocallyTreeLike A B B n := by
  intro S _
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B), ?_⟩
  let f : ↥(↑S : Set V) → V := Subtype.val
  have hf :
      (B.induce (↑S : Set V)).IsHomomorphismEmbedding B f :=
    (inclusion B (↑S : Set V)).isHomomorphismEmbedding
  refine ⟨f, hf, ?_⟩
  intro α
  refine ⟨α, ?_⟩
  intro a ha
  exact ⟨a, rfl⟩

end LocallyTreeLike

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.FreeAmalgam

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {D : RelStructure L U} {A : RelStructure L V}
variable {B : RelStructure L W} {Q : RelStructure L Y}
variable {fA : Embedding D A} {fB : Embedding D B}

/-- Fold a concrete free amalgam to a common target. -/
def fold
    (pA : V → Y) (pB : W → Y)
    (_hcompat : ∀ d, pA (fA d) = pB (fB d)) :
    Vertex D A B fA fB → Y
  | .inl a => pA a
  | .inr (_, b) => pB b.1

@[simp] theorem fold_left
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (a : V) :
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat (leftEmbedding D A B fA fB a) = pA a :=
  rfl

theorem fold_right
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (b : W) :
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat (rightEmbedding D A B fA fB b) = pB b := by
  classical
  by_cases hb : b ∈ support D A B fA fB
  · have hb' : ∃ d : U, fB d = b := by
      simpa [support] using hb
    rcases hb' with ⟨d, rfl⟩
    calc
      fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
          pA pB hcompat (rightEmbedding D A B fA fB (fB d)) =
        fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
          pA pB hcompat (leftEmbedding D A B fA fB (fA d)) := by
            exact congrArg
              (fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
                pA pB hcompat)
              (left_right_overlap D A B fA fB d).symm
      _ = pA (fA d) := fold_left pA pB hcompat (fA d)
      _ = pB (fB d) := hcompat d
  · change
      fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
        pA pB hcompat
        (Attachment.copyMap B (support D A B fA fB) A
          (fun _ : Unit => overlapEmbedding D A B fA fB) () b) = pB b
    rw [Attachment.copyMap_not_mem () b hb]
    rfl

/-- Compatible homomorphism-embeddings on the two sides of a concrete free
amalgam fold to a homomorphism-embedding into the common target. -/
theorem fold_isHomomorphismEmbedding
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (hpA : A.IsHomomorphismEmbedding Q pA)
    (hpB : B.IsHomomorphismEmbedding Q pB) :
    (amalgam D A B fA fB).IsHomomorphismEmbedding Q
      (fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
        pA pB hcompat) := by
  classical
  let F :=
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat
  constructor
  · intro R x hx
    change
      (Attachment.attach B (support D A B fA fB) A
        (fun _ : Unit => overlapEmbedding D A B fA fB)).rel R x at hx
    rcases hx with ⟨y, hy, hxy⟩ | ⟨i, y, hy, hxy⟩
    · have hQ : Q.rel R (pA ∘ y) := hpA.1 R y hy
      convert hQ using 1
      funext k
      have hk := congrFun hxy k
      change F (x k) = pA (y k)
      rw [hk]
      rfl
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      have hQ : Q.rel R (pB ∘ y) := hpB.1 R y hy
      convert hQ using 1
      funext k
      have hk := congrFun hxy k
      change F (x k) = pB (y k)
      rw [hk]
      exact fold_right pA pB hcompat (y k)
  · intro S hS
    let inc : Embedding ((amalgam D A B fA fB).induce S)
        (amalgam D A B fA fB) :=
      inclusion (amalgam D A B fA fB) S
    have hsplit :=
      Attachment.irreducible_core_or_copy
        (B := B) (S := support D A B fA fB) (D := A)
        (f := fun _ : Unit => overlapEmbedding D A B fA fB) S hS
    rcases hsplit with hcore | ⟨i, hcopy⟩
    · have hrange :
          ∀ z : S, ∃ a : V, inc z = leftEmbedding D A B fA fB a := by
        intro z
        rcases hcore z with ⟨a, ha⟩
        exact ⟨a, ha⟩
      let eA : Embedding ((amalgam D A B fA fB).induce S) A :=
        inc.factorThroughRange (leftEmbedding D A B fA fB) hrange
      obtain ⟨g, hg⟩ := hpA.after_irreducible_embedding hS eA
      refine ⟨g, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        g z = pA (eA z) := hg z
        _ = F (leftEmbedding D A B fA fB (eA z)) := by
          symm
          exact fold_left pA pB hcompat (eA z)
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      have hrange :
          ∀ z : S, ∃ b : W, inc z = rightEmbedding D A B fA fB b := by
        intro z
        rcases hcopy z with ⟨b, hb⟩
        exact ⟨b, hb⟩
      let eB : Embedding ((amalgam D A B fA fB).induce S) B :=
        inc.factorThroughRange (rightEmbedding D A B fA fB) hrange
      obtain ⟨g, hg⟩ := hpB.after_irreducible_embedding hS eB
      refine ⟨g, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        g z = pB (eB z) := hg z
        _ = F (rightEmbedding D A B fA fB (eB z)) := by
          symm
          exact fold_right pA pB hcompat (eB z)
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm

/-- Attach one fresh copy of \`B\` over an irreducible substructure while
preserving a homomorphism-embedding into a common target \`Q\`.

It is enough that the projected overlap is contained in the image of one
embedding \`β : B ↪ Q\`.  The embedding of the overlap into the fresh copy of
\`B\` is reconstructed from the homomorphism-embedding property on the
irreducible overlap. -/
theorem attachOverIrreducible_preservesProjection
    (hD : D.Irreducible)
    (pA : V → Y)
    (hpA : A.IsHomomorphismEmbedding Q pA)
    (β : Embedding B Q)
    (hcover : ∀ d : U, ∃ b : W, pA (fA d) = β b) :
    ∃ fB : Embedding D B,
      ∃ p : Vertex D A B fA fB → Y,
        (amalgam D A B fA fB).IsHomomorphismEmbedding Q p ∧
        (∀ a : V, p (leftEmbedding D A B fA fB a) = pA a) ∧
        ∀ b : W, p (rightEmbedding D A B fA fB b) = β b := by
  classical
  obtain ⟨eDQ, heDQ⟩ :=
    hpA.after_irreducible_embedding hD fA
  have hrange : ∀ d : U, ∃ b : W, eDQ d = β b := by
    intro d
    obtain ⟨b, hb⟩ := hcover d
    exact ⟨b, (heDQ d).trans hb⟩
  let fB' : Embedding D B :=
    eDQ.factorThroughRange β hrange
  have hcompat : ∀ d : U, pA (fA d) = β (fB' d) := by
    intro d
    calc
      pA (fA d) = eDQ d := (heDQ d).symm
      _ = β (fB' d) := by
        change eDQ d = β (Classical.choose (hrange d))
        exact Classical.choose_spec (hrange d)
  let p : Vertex D A B fA fB' → Y :=
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB')
      pA β hcompat
  have hp :
      (amalgam D A B fA fB').IsHomomorphismEmbedding Q p := by
    exact fold_isHomomorphismEmbedding pA β hcompat
      hpA β.isHomomorphismEmbedding
  refine ⟨fB', p, hp, ?_, ?_⟩
  · intro a
    exact fold_left pA β hcompat a
  · intro b
    exact fold_right pA β hcompat b

end StructuralRamsey.RelStructure.FreeAmalgam


namespace StructuralRamsey.RelStructure.LocallyTreeLike

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H X : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {D : RelStructure L H} {Core : RelStructure L X}
variable {fCore : Embedding D Core} {fBase : Embedding D Base}

/-- A single final free attachment preserves the strengthened local-tree
invariant when the common overlap is hereditarily irreducible.

The hereditary hypothesis is used only for an arbitrary intersection of the
tested finite set with the gluing overlap: the homomorphism-embedding on the
old side must restrict there to a genuine embedding before the two tree
witnesses can be glued. -/
theorem freeAmalgam
    [Finite UA] [Finite VB] [Finite H] [Finite X]
    (hControl : HereditarilyIrreducible Control)
    (eControlBase : Embedding Control Base)
    (hD : HereditarilyIrreducible D)
    (n : ℕ)
    (hCore : LocallyTreeLike Control Base Core n) :
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

  let Piece :=
    Attachment.Piece Base Support Core g Tset ()
  let Rest :=
    Attachment.Rest Base Support Core g Tset ()
  let Overlap :=
    Attachment.Overlap Base Support Core g Tset ()
  let PieceV :=
    Attachment.PieceV Base Support Core g Tset ()
  let RestV :=
    Attachment.RestV (W := X) (I := Unit) Support Tset ()
  let OverlapV :=
    Attachment.OverlapV Base Support Core g Tset ()
  let sPiece :=
    Attachment.overlapToPiece Base Support Core g Tset ()
  let sRest :=
    Attachment.overlapToRest Base Support Core g Tset ()
  let iPiece :=
    Attachment.pieceInclusion Base Support Core g Tset ()
  let iRest :=
    Attachment.restInclusion Base Support Core g Tset ()

  have hFree : IsFreeAmalgam sPiece sRest iPiece iRest := by
    exact Attachment.decompose Base Support Core g Tset ()

  let l := FreeAmalgam.leftEmbedding D Core Base fCore fBase
  let r := FreeAmalgam.rightEmbedding D Core Base fCore fBase
  let ePieceWhole : Embedding Piece Whole :=
    smallIncl.comp iPiece
  let eRestWhole : Embedding Rest Whole :=
    smallIncl.comp iRest

  have hPieceRange :
      ∀ z : PieceV, ∃ b : VB, ePieceWhole z = r b := by
    intro z
    rcases z.2 with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact hb

  have hRestRange :
      ∀ z : RestV, ∃ x : X, eRestWhole z = l x := by
    intro z
    cases hz : z.1.1 with
    | inl x =>
        exact ⟨x, hz⟩
    | inr pair =>
        rcases pair with ⟨i, b⟩
        have hi : i = () := Subsingleton.elim _ _
        subst i
        exact (z.2 ⟨b, hz⟩).elim

  let ePiece : Embedding Piece Base :=
    ePieceWhole.factorThroughRange r hPieceRange
  let eRest : Embedding Rest Core :=
    eRestWhole.factorThroughRange l hRestRange

  have hPieceSpec (z : PieceV) :
      ePieceWhole z = r (ePiece z) := by
    change ePieceWhole z = r (Classical.choose (hPieceRange z))
    exact Classical.choose_spec (hPieceRange z)
  have hRestSpec (z : RestV) :
      eRestWhole z = l (eRest z) := by
    change eRestWhole z = l (Classical.choose (hRestRange z))
    exact Classical.choose_spec (hRestRange z)

  have hOverlapRange :
      ∀ z : OverlapV, ∃ d : H, eRest (sRest z) = fCore d := by
    intro z
    have hsmall :
        iPiece (sPiece z) = iRest (sRest z) :=
      (hFree.overlap (sPiece z) (sRest z)).mpr ⟨z, rfl, rfl⟩
    have hwhole :
        l (eRest (sRest z)) = r (ePiece (sPiece z)) := by
      calc
        l (eRest (sRest z)) = eRestWhole (sRest z) :=
          (hRestSpec (sRest z)).symm
        _ = ePieceWhole (sPiece z) := by
          change smallIncl (iRest (sRest z)) =
            smallIncl (iPiece (sPiece z))
          exact congrArg smallIncl hsmall.symm
        _ = r (ePiece (sPiece z)) :=
          hPieceSpec (sPiece z)
    obtain ⟨d, hdCore, _⟩ :=
      ((FreeAmalgam.isFreeAmalgam D Core Base fCore fBase).overlap
        (eRest (sRest z)) (ePiece (sPiece z))).mp hwhole
    exact ⟨d, hdCore⟩

  let eOverlapD : Embedding Overlap D :=
    (eRest.comp sRest).factorThroughRange fCore hOverlapRange
  have hOverlapIrreducible : Overlap.Irreducible :=
    hD.of_embedding eOverlapD

  letI : Fintype Tset := Fintype.ofFinite Tset
  letI : Fintype RestV := Fintype.ofFinite RestV
  have hRestCard : Fintype.card RestV ≤ n := by
    calc
      Fintype.card RestV ≤ Fintype.card Tset :=
        Fintype.card_le_of_injective
          (fun z : RestV => z.1)
          (by
            intro a b hab
            apply Subtype.ext
            exact hab)
      _ ≤ n := by
        simpa [Tset] using hScard

  have hRestLTL : LocallyTreeLike Control Base Rest n :=
    hCore.pullback_embedding eRest
  obtain ⟨YR, TR, hTreeR, pRest, hpRest, ctrlRest⟩ :=
    hRestLTL.fullWitness hRestCard

  let pPiece : PieceV → VB := ePiece
  have hpPiece : Piece.IsHomomorphismEmbedding Base pPiece :=
    ePiece.isHomomorphismEmbedding
  have ctrlPiece :
      ∀ α : Embedding Control Piece,
        ∃ α' : Embedding Control Base,
          ∀ a : UA, ∃ a' : UA, pPiece (α a) = α' a' := by
    intro α
    let α' : Embedding Control Base := ePiece.comp α
    refine ⟨α', ?_⟩
    intro a
    exact ⟨a, rfl⟩

  let tPiece : Embedding Overlap Base := ePiece.comp sPiece
  obtain ⟨tRest, htRest⟩ :=
    hpRest.after_irreducible_embedding hOverlapIrreducible sRest

  obtain ⟨Y, T, hTree, pSmall, hpSmall, _⟩ :=
    glueControlled
      (tE := tPiece) (tF := tRest)
      hControl.irreducible hFree hOverlapIrreducible
      (TreeAmalgam.copy (Iso.refl Base)) hTreeR
      (fun z : OverlapV => z) pPiece pRest
      (fun _ => rfl) (fun z => (htRest z).symm)
      hpPiece hpRest ctrlPiece ctrlRest

  have hpSmall' :
      (Whole.induce (↑S : Set _)).IsHomomorphismEmbedding T pSmall := by
    simpa [Small, Tset, Whole] using hpSmall
  exact completeControl
    (A := Control) (B := Base) (C := Whole)
    hControl eControlBase S hTree pSmall hpSmall'

end StructuralRamsey.RelStructure.LocallyTreeLike

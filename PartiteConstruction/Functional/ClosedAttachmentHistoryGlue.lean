import PartiteConstruction.Functional.HistoryMixedGlue
import PartiteConstruction.Functional.BoundaryDiary

/-! # Mixed history gluing for closed functional attachments

This specializes the generic functional mixed-history theorem to the named
full-structure decomposition of a closed test in a closed partite attachment.
It is deliberately bookkeeping-only: the caller supplies the two side
relative-history invariants and the common A-labelling of the overlap.
-/

namespace StructuralRamsey.Partite.Closed.Attachment

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v

variable {L : Language.{u}}
variable {P0 V0 W0 I0 U P VB : Type v}
variable {A : Structure L U} {Dbase : Structure L P}
variable {Base : Structure L VB}

variable (Bsys : Partite.System L.graph P0 V0) (Supp : Set V0)
variable (Dsys : Partite.System L.graph P0 W0)
variable (maps0 : I0 → Partite.Closed.Embedding (Bsys.induce Supp) Dsys)
variable (Test : Set
  (Partite.Attachment.Vertex Supp (W := W0) (I := I0)))
variable (idx : I0)

/-- The current overlap, viewed as a projected boundary request on the rest
side.  This is the diary entry passed to the recursive call after peeling off
the selected attached copy. -/
noncomputable def restProjectedBoundaryRequest
    (hSupp : RelStructure.FunctionClosedSet Bsys.toRelStructure Supp)
    (pSmall : ↥Test → P)
    (β : Structure.Embedding A Dbase)
    (ell :
      Structure.Embedding
        (FullOverlap Bsys Supp Dsys maps0 Test idx) A)
    (hprojRest :
      ∀ d,
        pSmall
            (fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp
              (fullOverlapToRest
                Bsys Supp Dsys maps0 Test idx hSupp d)) =
          β (ell d)) :
    _root_.StructuralRamsey.Structure.ProjectedBoundaryRequest
      A Dbase
      (FullRest Bsys Supp Dsys maps0 Test idx)
      (pSmall ∘
        fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp) :=
  _root_.StructuralRamsey.Structure.ProjectedBoundaryRequest.ofEmbeddedLabels
    ell β
    (fullOverlapToRest Bsys Supp Dsys maps0 Test idx hSupp)
    hprojRest

/-- Recursive one-copy peel.  The selected piece is solved from its
relative-history invariant.  The rest is supplied by the recursive call and
already isolates the current overlap (in normalized diary form) together with
any older boundaries.  Gluing preserves the requested source history and
transports every older boundary into the whole test. -/
theorem gluePieceWithRestDiary
    (hSupp : RelStructure.FunctionClosedSet Bsys.toRelStructure Supp)
    (hA : A.Irreducible)
    (pSmall : ↥Test → P)
    (β : Structure.Embedding A Dbase)
    (ell :
      Structure.Embedding
        (FullOverlap Bsys Supp Dsys maps0 Test idx) A)
    (hprojPiece :
      ∀ d,
        pSmall
            (fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp
              (fullOverlapToPiece
                Bsys Supp Dsys maps0 Test idx hSupp d)) =
          β (ell d))
    {n : ℕ}
    [Fintype
      (RelStructure.Attachment.PieceV
        Bsys.toRelStructure Supp Dsys.toRelStructure
        (fun j => (maps0 j).1.toEmbedding) Test idx)]
    (hPiece :
      _root_.StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike
        (A := A) (D := Dbase)
        (C := FullPiece Bsys Supp Dsys maps0 Test idx)
        (Base := Base)
        (pSmall ∘
          fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp) n)
    (hgenPiece :
      (FullPiece Bsys Supp Dsys maps0 Test idx).GeneratedByAtMost n)
    (history : List (Set ↥Test))
    {ZR : Type v} {TR : Structure L ZR}
    (hTreeR : TreeAmalgam Base ZR TR)
    (fR :
      RelStructure.Attachment.RestV
        (W := W0) (I := I0) Supp Test idx → ZR)
    (hfR :
      _root_.StructuralRamsey.Structure.IsHomomorphismEmbedding
        (FullRest Bsys Supp Dsys maps0 Test idx) TR fR)
    (hHistR :
      ∀ Hset ∈ history,
        ∀ x y :
          RelStructure.Attachment.RestV
            (W := W0) (I := I0) Supp Test idx,
          fR x = fR y →
            (fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp x ∈ Hset ↔
             fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp y ∈ Hset))
    (hCurrent :
      _root_.StructuralRamsey.Structure.IsolatedBoundary
        (_root_.StructuralRamsey.Structure.BoundaryRequest.ofEmbeddedLabels
          ell
          (fullOverlapToRest
            Bsys Supp Dsys maps0 Test idx hSupp))
        TR fR)
    (oldRequests :
      List
        (_root_.StructuralRamsey.Structure.BoundaryRequest
          A (FullRest Bsys Supp Dsys maps0 Test idx)))
    (hDiaryR :
      ∀ r ∈ oldRequests,
        _root_.StructuralRamsey.Structure.IsolatedBoundary r TR fR) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥Test → Z,
        _root_.StructuralRamsey.Structure.IsHomomorphismEmbedding
          (FullSmall Bsys Supp Dsys maps0 Test) Target f ∧
        (∀ Hset ∈ history, ∀ x y : ↥Test,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) ∧
        ∀ r ∈ oldRequests,
          _root_.StructuralRamsey.Structure.IsolatedBoundary
            (r.postcomp
              (fullRestInclusion
                Bsys Supp Dsys maps0 Test idx hSupp))
            Target f := by
  classical
  let sL :=
    fullOverlapToPiece Bsys Supp Dsys maps0 Test idx hSupp
  let sR :=
    fullOverlapToRest Bsys Supp Dsys maps0 Test idx hSupp
  let iL :=
    fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp
  let iR :=
    fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp
  let hfree :=
    full_decompose_named
      Bsys Supp Dsys maps0 Test idx hSupp
  let historyL :
      List
        (Set
          (RelStructure.Attachment.PieceV
            Bsys.toRelStructure Supp Dsys.toRelStructure
            (fun j => (maps0 j).1.toEmbedding) Test idx)) :=
    history.map (fun Hset => iL ⁻¹' Hset)
  obtain ⟨ZL, TL, hTreeL, fL, hfL, _hPartL, _hProjL, hHistL0,
    targetL, hcompatL, hisoL⟩ :=
    hPiece.fullWitness_embeddedLabels
      hgenPiece [] historyL ell β sL
      (fun d => hprojPiece d)
  have hrootL :
      _root_.StructuralRamsey.Structure.IsFreeAmalgam.RootIsolated
        sL targetL ell fL := by
    intro x a hxa
    obtain ⟨d, hxd, hda⟩ := hisoL x a hxa
    exact ⟨d, hxd, hda⟩
  have hHistL :
      ∀ Hset ∈ history,
        ∀ x y :
          RelStructure.Attachment.PieceV
            Bsys.toRelStructure Supp Dsys.toRelStructure
            (fun j => (maps0 j).1.toEmbedding) Test idx,
          fL x = fL y → (iL x ∈ Hset ↔ iL y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hpre : iL ⁻¹' Hset ∈ historyL := by
      apply List.mem_map.mpr
      exact ⟨Hset, hmem, rfl⟩
    exact hHistL0 (iL ⁻¹' Hset) hpre x y hxy
  obtain ⟨targetR, hcompatR, hrootR⟩ :=
    _root_.StructuralRamsey.Structure.IsolatedBoundary.toEmbeddedLabels
      ell sR hCurrent
  simpa [sL, sR, iL, iR] using
    (_root_.StructuralRamsey.Structure.IsFreeAmalgam.glueIsolatedCommonLabels_withHistoryAndRightDiary
      (A := A) (Base := Base)
      hA hfree hTreeL hTreeR targetL targetR ell ell.injective
      fL fR hcompatL hcompatR hfL hfR hrootL hrootR
      history hHistL hHistR oldRequests hDiaryR)

/-- Glue relative-history witnesses for the two closed sides of one chosen
attached copy. -/
theorem glueRelativeHistory
    (hSupp : RelStructure.FunctionClosedSet Bsys.toRelStructure Supp)
    (hA : A.Irreducible)
    (pSmall : ↥Test → P)
    (β : Structure.Embedding A Dbase)
    (ell :
      Structure.Embedding
        (FullOverlap Bsys Supp Dsys maps0 Test idx) A)
    (hprojPiece :
      ∀ d,
        pSmall
            (fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp
              (fullOverlapToPiece
                Bsys Supp Dsys maps0 Test idx hSupp d)) =
          β (ell d))
    (hprojRest :
      ∀ d,
        pSmall
            (fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp
              (fullOverlapToRest
                Bsys Supp Dsys maps0 Test idx hSupp d)) =
          β (ell d))
    {n : ℕ}
    [Fintype
      (RelStructure.Attachment.PieceV
        Bsys.toRelStructure Supp Dsys.toRelStructure
        (fun j => (maps0 j).1.toEmbedding) Test idx)]
    [Fintype
      (RelStructure.Attachment.RestV
        (W := W0) (I := I0) Supp Test idx)]
    (hPiece :
      _root_.StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike
        (A := A) (D := Dbase)
        (C := FullPiece Bsys Supp Dsys maps0 Test idx)
        (Base := Base)
        (pSmall ∘
          fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp) n)
    (hRest :
      _root_.StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike
        (A := A) (D := Dbase)
        (C := FullRest Bsys Supp Dsys maps0 Test idx)
        (Base := Base)
        (pSmall ∘
          fullRestInclusion Bsys Supp Dsys maps0 Test idx hSupp) n)
    (hgenPiece :
      (FullPiece Bsys Supp Dsys maps0 Test idx).GeneratedByAtMost n)
    (hgenRest :
      (FullRest Bsys Supp Dsys maps0 Test idx).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set ↥Test)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥Test → Z,
        _root_.StructuralRamsey.Structure.IsHomomorphismEmbedding
          (FullSmall Bsys Supp Dsys maps0 Test) Target f ∧
        (∀ Hset ∈ projectedHistory, ∀ x y : ↥Test,
          f x = f y → (pSmall x ∈ Hset ↔ pSmall y ∈ Hset)) ∧
        (∀ Hset ∈ sourceHistory, ∀ x y : ↥Test,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) := by
  let hfree :=
    full_decompose_named
      Bsys Supp Dsys maps0 Test idx hSupp
  exact
    _root_.StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike.glueWholeWitnesses
      (A := A) (D := Dbase) (Base := Base)
      hA hfree pSmall β ell hprojPiece hprojRest
      hPiece hRest hgenPiece hgenRest projectedHistory sourceHistory

end StructuralRamsey.Partite.Closed.Attachment

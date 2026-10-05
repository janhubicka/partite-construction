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

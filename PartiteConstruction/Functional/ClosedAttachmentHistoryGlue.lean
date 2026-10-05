import PartiteConstruction.Functional.HistoryMixedGlue

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

/-- Glue relative-history witnesses for the two closed sides of one chosen
attached copy. -/
theorem glueRelativeHistory
    (hSupp : RelStructure.FunctionClosedSet Bsys.toRelStructure Supp)
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
      Structure.FunctionalRelativeHistoryTreeLike
        (A := A) (D := Dbase)
        (C := FullPiece Bsys Supp Dsys maps0 Test idx)
        (Base := Base)
        (pSmall ∘
          fullPieceInclusion Bsys Supp Dsys maps0 Test idx hSupp) n)
    (hRest :
      Structure.FunctionalRelativeHistoryTreeLike
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
        (FullSmall Bsys Supp Dsys maps0 Test).
          IsHomomorphismEmbedding Target f ∧
        (∀ Hset ∈ projectedHistory, ∀ x y : ↥Test,
          f x = f y → (pSmall x ∈ Hset ↔ pSmall y ∈ Hset)) ∧
        (∀ Hset ∈ sourceHistory, ∀ x y : ↥Test,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) := by
  let hfree :=
    full_decompose_named
      Bsys Supp Dsys maps0 Test idx hSupp
  exact
    Structure.FunctionalRelativeHistoryTreeLike.glueWholeWitnesses
      (A := A) (D := Dbase) (Base := Base)
      (hA := by
        -- The irreducibility hypothesis is read from the relative witness
        -- only at the actual glue; make it explicit to the caller below.
        exact Classical.choice (show Nonempty A.Irreducible from ?_))
      hfree pSmall β ell hprojPiece hprojRest
      hPiece hRest hgenPiece hgenRest projectedHistory sourceHistory

end StructuralRamsey.Partite.Closed.Attachment

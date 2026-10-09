import PartiteConstruction.Ramsey.ClosurePartitePower
import PartiteConstruction.Ramsey.ClosureAttachmentClosed
import PartiteConstruction.Ramsey.ClosurePictureCoordinate
import PartiteConstruction.Partite.InducedPicture

/-! # A closed witness for the native induced Picture Lemma

All partite embeddings of the restricted old structure are used, exactly
as in Picture.build. This is not just a line-indexed surrogate. Closedness
of the restricted support, coordinate core, and full multi-attachment is
proved from closed input structures and ordinary partiteness.

The finite Hales--Jewett witness therefore satisfies the original local
PictureProperty AND U-closedness. Protected-copy coverage and the stronger
protected core projection are separate obligations, not conclusions of
this local Ramsey/closedness theorem. No complete rank increment or literal
2019 multiamalgamation theorem is claimed here.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V I X : Type v}

/-- The selected support is relatively closed because its part labels
lie in a closed embedded part structure. No source-closedness premise is
needed for this relative assertion. -/
theorem support_isUSubstructure_of_closed_part_copy
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hPart : B.IsPartiteOver D) :
    IsUSubstructure rules B.toRelStructure (B.support alpha.toFunctionEmbedding) := by
  exact (alpha.range_isUSubstructure hA hD).preimage_homomorphism hPart.1

/-- The actual all-embeddings Picture.build over a positive coordinate
power is closed, not merely the selected line-indexed subattachment. -/
theorem picture_build_power_isUClosed
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure) (hPart : B.IsPartiteOver D)
    (N : ℕ) (hN : 0 < N) :
    IsUClosed rules
      (Picture.build B alpha.toFunctionEmbedding
        (power (B.restrict alpha.toFunctionEmbedding) N)).toRelStructure := by
  let af := alpha.toFunctionEmbedding
  let R := B.restrict af
  let E := power R N
  have hSupport : IsUSubstructure rules B.toRelStructure (B.support af) :=
    support_isUSubstructure_of_closed_part_copy A D B alpha hA hD hPart
  have hR : IsUClosed rules R.toRelStructure :=
    hB.induce_of_USubstructure (B.support af) hSupport
  have hPartR : R.IsPartiteOver A := restrict_isPartiteOver D B A hPart alpha
  have hE : IsUClosed rules E.toRelStructure :=
    power_isUClosed R hPartR hA hR hN
  exact RelStructure.Attachment.attach_isUClosed B.toRelStructure (B.support af)
    (E.relabel af).toRelStructure
    (fun i => (Picture.attachingMap B af E i).toEmbedding) hB hE hSupport

/-- Finite native induced Picture Lemma with a U-closed witness.
Ordinary partiteness and PictureProperty are retained. No protected-test
projection or coverage hypothesis is smuggled into the conclusion. -/
theorem pictureLemma_isUClosed
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure) (hPart : B.IsPartiteOver D)
    [Finite Q] [Finite V] (Color : Type*) [Fintype Color] :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      C.IsPartiteOver D ∧ IsUClosed rules C.toRelStructure ∧
      PictureProperty A B alpha.toFunctionEmbedding C Color := by
  classical
  let af := alpha.toFunctionEmbedding
  let R := B.restrict af
  have hPartR : R.IsPartiteOver A := restrict_isPartiteOver D B A hPart alpha
  obtain ⟨N, hN, hArrow⟩ := partiteLemma (A := A) (B := R) hPartR Color
  let E := power R N
  have hPartE : E.IsPartiteOver A := power_isPartiteOver hPartR hN
  have hCore : (E.relabel af).IsPartiteOver D :=
    relabel_isPartiteOver (A := A) (B := E) hPartE alpha
  let C := Picture.build B af E
  have hC : C.IsPartiteOver D :=
    Attachment.attach_isPartiteOver B (B.support af) (E.relabel af)
      (Picture.attachingMap B af E) hPart hCore
  exact ⟨Picture.Vertex B af E, inferInstance, C, hC,
    picture_build_power_isUClosed A D B alpha hA hD hB hPart N hN,
    Picture.property B af E Color hArrow⟩

/-- The line-indexed native attachment used by the local-coordinate
completion branch is closed as well. The stronger protected core map
is NOT needed to establish this closedness. -/
theorem line_attachment_isUClosed
    {rules : ClosureDescription L} {N : ℕ}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hA : IsUClosed rules A) (hN : 0 < N) :
    IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) := by
  have hRestrictedClosed : IsUClosed rules (Old.restrict alpha).toRelStructure :=
    hOld.induce_of_USubstructure (Old.support alpha) hSupport
  exact RelStructure.Attachment.attach_isUClosed
    Old.toRelStructure (Old.support alpha)
    (power (Old.restrict alpha) N).toRelStructure
    (closureLineMaps Old alpha A hRestricted lines) hOld
    (power_isUClosed (Old.restrict alpha) hRestricted hA hRestrictedClosed hN)
    hSupport

/-- The earlier local coordinate completion theorem now needs no assumed
whole-attachment closedness. It follows from the closed old structure,
closed part structure and relatively closed support. The protected core
projection and the local common-coordinate premise remain explicit. -/
theorem completion_of_common_coordinate_from_closed_pieces
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L} {N : ℕ}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hA : IsUClosed rules A)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ n →
        HasClosedUKCompletion K rules (Old.toRelStructure.induce T))
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n) (k : Fin N)
    (hActive : ∀ g ∈ G, ∀ i,
      RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
        (lines i).symbol k = .parameter) :
    HasClosedUKCompletion K rules Test := by
  have hWhole := line_attachment_isUClosed Old alpha A hRestricted lines
    hOld hSupport hA (Nat.zero_lt_of_lt k.isLt)
  exact completion_of_common_generator_coordinate Old alpha A hRestricted lines
    hOld hSupport hPower hWhole n hRank Test e G hGen hSize k hActive

end StructuralRamsey.Partite.Induced

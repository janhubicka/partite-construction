import PartiteConstruction.Ramsey.ClosureLinePictureRamsey
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Partite.InducedAttachment

/-! # A single actual little Picture with both required properties

The unrestricted recursive proof of Lemma 2.28 needs TWO facts about
the SAME temporarily conflicting line-indexed little Picture O:

(1) O has the local PictureProperty for selected copies of A.
(2) Every U-CLOSED A-profile copy with those selected parts has
    relatively U-closed range in O.

Property (1) was just proved by the exact line-family Hales--Jewett
argument, not by switching to the all-embeddings attachment.
Property (2) comes from the semi-closed-core root safety lemma:
the old attachment support can omit closure outputs and O itself
need not be semi-closed.

The proof also retains ordinary D-partiteness of the whole O.
It does not assert that O has a protected projection, is U-closed,
or has a K-completion. The subsequent repaired Lemma 2.29 is what
must turn this temporary picture into a closed protected one.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v}

/-- A CLOSED old picture with a closed-test protected projection is an
ordinary partite system over D. Thus for ANY induced A-copy in a
possibly nonclosed D its exact selected part restriction is ordinarily
A-partite: no additional assumption on the restriction is necessary. -/
theorem restrictedPartite_of_closedProtected
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (Old : System L P V) (alpha : RelStructure.Embedding A D)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules Old.toRelStructure D Old.part) :
    (Old.restrict alpha.toFunctionEmbedding).IsPartiteOver A := by
  have hOrdinary : Old.IsPartiteOver D :=
    hPart.toHomomorphismEmbedding_of_closed hOld
  exact restrict_isPartiteOver D Old A hOrdinary alpha

/-- Every canonical line-family attachment is ordinary D-partite
if the old picture and exact restricted power have their ordinary
partite projections. This needs no U-closedness of the attachment. -/
theorem familyPicture_isPartiteOver
    (A : RelStructure L Q) (D : RelStructure L P)
    (Old : System L P V) (alpha : RelStructure.Embedding A D)
    (hOldPart : Old.IsPartiteOver D)
    (hR : (Old.restrict alpha.toFunctionEmbedding).IsPartiteOver A)
    (N : ℕ) (hN : 0 < N) :
    (familyPicture Old alpha.toFunctionEmbedding
      (power (Old.restrict alpha.toFunctionEmbedding) N)
      (fun line : Line (Letter A (Old.restrict alpha.toFunctionEmbedding)) N =>
        lineEmbedding hR line)).IsPartiteOver D := by
  let af := alpha.toFunctionEmbedding
  let R := Old.restrict af
  let E := power R N
  have hPower : E.IsPartiteOver A := power_isPartiteOver hR hN
  have hCore : (E.relabel af).IsPartiteOver D :=
    relabel_isPartiteOver A E hPower alpha
  exact Partite.Attachment.attach_isPartiteOver
    Old (Old.support af) (E.relabel af)
      (fun line : Line (Letter A R) N =>
        Partite.Picture.attachingMap Old af E (lineEmbedding hR line))
    hOldPart hCore

/-- The SAME finite native little Picture satisfies its local Ramsey
property, ordinary projection invariant, and the required relative
closure of ALL embedded selected-profile closed tests. The OLD source
is closed; D itself may be arbitrarily nonclosed. -/
theorem semiClosed_littlePicture_selected_relative
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (Old : System L P V) (alpha : RelStructure.Embedding A D)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hOldPart : Old.IsPartiteOver D)
    (hR : (Old.restrict alpha.toFunctionEmbedding).IsPartiteOver A)
    [Finite Q] [Finite V]
    (Color : Type*) [Fintype Color] :
    ∃ N : ℕ, 0 < N ∧
      let af := alpha.toFunctionEmbedding
      let R := Old.restrict af
      let O := familyPicture Old af (power R N)
        (fun line : Line (Letter A R) N => lineEmbedding hR line)
      O.IsPartiteOver D ∧
      Partite.PictureProperty A Old af O Color ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test →
        ∀ e : RelStructure.Embedding Test O.toRelStructure,
          (∀ x, O.part (e x) ∈ Set.range af) →
          IsUSubstructure rules O.toRelStructure (Set.range e)) := by
  have hSemi : IsUSemiClosed rules Old.toRelStructure := hOld.isUSemiClosed
  obtain ⟨N, hN, hPicture⟩ :=
    semiClosed_familyPictureProperty A Old alpha.toFunctionEmbedding
      hR hSemi Color
  refine ⟨N, hN, ?_, hPicture, ?_⟩
  · exact familyPicture_isPartiteOver A D Old alpha hOldPart hR N hN
  · intro X Test hTest e hSel
    have hProfile : ∀ x,
        RelStructure.Attachment.fold
          (fun z : Vertex (Old.restrict alpha.toFunctionEmbedding) N =>
            alpha.toFunctionEmbedding z.part)
          (fun _ : Line (Letter A (Old.restrict alpha.toFunctionEmbedding)) N =>
            Old.part) (e x) ∈ Set.range alpha.toFunctionEmbedding := by
      intro x
      exact hSel x
    exact closed_profile_in_native_line_attachment Old
      alpha.toFunctionEmbedding A hR hOld hN
      (fun line => line) Test hTest e hProfile

end StructuralRamsey.Partite.Induced

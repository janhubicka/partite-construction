import PartiteConstruction.Ramsey.ClosureTaggedOuterProtected
import PartiteConstruction.Ramsey.ClosureTaggedLittlePicture
import PartiteConstruction.Ramsey.ClosureLittlePictureSelected

/-! # The unrestricted repaired local Picture refinement

This proves the missing one-step lemma for Lemma 2.28: the original
control D may be nonclosed and the actual attaching support may omit
closure outputs. The native little Picture can have conflicting
closure outputs, so it is NEVER assumed U-semi-closed.

Actual construction, not a witness oracle:
1. Restrict Old to the exact selected parts and build the canonical
   Hales--Jewett line-family little Picture O.
2. O is ordinarily D-partite, has the real local PictureProperty, and
   every closed selected-profile test has relatively closed range.
3. Apply the already proved relative-copy theorem to O in the
   correctly root-tagged part language, constructing a tagged-closed
   Ramsey witness T with protection and coverage by Old_tag.
4. Normalize T and descend to the OLD language as a finite, U-closed,
   outer D-partite picture New.
5. Transport the tagged Ramsey arrow back to PictureProperty, and
   use ACTUAL closed test coverage by Old_tag to prove that the outer
   New-to-D projection is protected. Every protected closed test of
   New embeds into Old.

An actual selected A-copy inside Old is an explicit premise, as in
the nontrivial/relevant embedding branch of the outer finite pass.
No rank increment is asserted; the higher-rank j->j+1 construction
remains a logically separate task.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v}

/-- A real unrestricted local Picture refinement, preserving all
closed-test invariants, for ANY induced A-copy alpha in a possibly
nonclosed D as long as an alpha-profile A-copy exists in Old. -/
theorem pictureLemma_protected_unrestricted
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (Old : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hOldPart : IsClosedUHomomorphismEmbedding rules
      Old.toRelStructure D Old.part)
    (aOld : Partite.ProjectedEmbedding A Old alpha.toFunctionEmbedding)
    [Finite Q] [Finite V]
    (Color : Type*) [Fintype Color] [Nonempty Color] :
    ∃ (Y : Type v) (_ : Finite Y) (New : System L P Y),
      Partite.PictureProperty A Old alpha.toFunctionEmbedding New Color ∧
      IsUClosed rules New.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules New.toRelStructure D New.part ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test New.toRelStructure →
        Nonempty (RelStructure.Embedding Test Old.toRelStructure)) := by
  classical
  let af := alpha.toFunctionEmbedding
  let R := Old.restrict af
  have hOrdinary : Old.IsPartiteOver D :=
    hOldPart.toHomomorphismEmbedding_of_closed hOld
  have hR : R.IsPartiteOver A :=
    restrictedPartite_of_closedProtected A D Old alpha hOld hOldPart
  obtain ⟨N, hN, hOOrd, hOPicture, hOSelected⟩ :=
    semiClosed_littlePicture_selected_relative
      A D Old alpha hOld hOrdinary hR Color
  let Index := Line (Letter A R) N
  let O : System L P (RelStructure.Attachment.Vertex (Old.support af)
      (W := Vertex R N) (I := Index)) :=
    familyPicture Old af (power R N)
      (fun line : Index => lineEmbedding hR line)
  have hOOrd' : O.IsPartiteOver D := hOOrd
  have hOPicture' : Partite.PictureProperty A Old af O Color := hOPicture
  have hOSelected' : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      ∀ e : RelStructure.Embedding Test O.toRelStructure,
        (∀ x, O.part (e x) ∈ Set.range af) →
        IsUSubstructure rules O.toRelStructure (Set.range e) := hOSelected
  letI : Finite Index := inferInstance
  letI : Finite (Vertex R N) := inferInstance
  letI : Finite (RelStructure.Attachment.Vertex (Old.support af)
      (W := Vertex R N) (I := Index)) := inferInstance
  obtain ⟨Y, hY, T, hRamseyTag, hT, hProj, hCover⟩ :=
    taggedRepair_of_littlePicture rules A Old af O
      hA hOld aOld Color hOPicture' hOSelected'
  let C : System L P Y :=
    taggedWitnessOuterSystem rules D O T hT hProj hOOrd'
  have hClosed : IsUClosed rules C.toRelStructure :=
    taggedWitnessOuterSystem_isUClosed rules D O T hT hProj hOOrd'
  have hPart : IsClosedUHomomorphismEmbedding rules C.toRelStructure
      D C.part :=
    taggedWitnessOuter_protected D Old O T hT hProj hOOrd' hOldPart hCover
  have hNormal : T.toRelStructure =
      RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part :=
    tagged_closed_source_normalizes_of_protected
      rules T.toRelStructure O.toRelStructure O.part T.part hT hProj
  have hArrowC : StructuralRamsey.Arrow
      (RelStructure.expandTaggedClosureParts rules A af)
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part)
      (RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part)
      Color := by
    rw [← hNormal]
    exact hRamseyTag
  have hPictureC : Partite.PictureProperty A Old af C Color :=
    pictureProperty_of_taggedArrow rules A Old af C Color hArrowC
  refine ⟨Y, hY, C, hPictureC, hClosed, hPart, ?_⟩
  intro X Test hTestClosed hTestIrred e
  obtain ⟨gOld, _⟩ := taggedWitnessOuter_closedTest_in_old
    D Old O T hT hProj hOOrd' hCover
      Test hTestClosed hTestIrred e
  exact ⟨gOld⟩

end StructuralRamsey.Partite.Induced

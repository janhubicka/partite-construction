import PartiteConstruction.Ramsey.ClosureLittlePictureSelected
import PartiteConstruction.Ramsey.ClosureTaggedRank
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey

/-! # The exact tagged-language interface to the recursive little Picture

The first two theorems translate the genuine local PictureProperty and
selected U-closed-copy relative-substructure condition into the tagged
language of the repaired relative-copy Ramsey lemma.

The last theorem performs ONE ACTUAL inner application of that verified
relative-copy theorem: starting with an old U-closed picture, a finite
temporary little Picture satisfying the local Ramsey/selected-range
conditions, and an existing projected A-copy in Old, it constructs a
new tagged-U-closed Ramsey witness. All tagged closed irreducible tests
of the resulting witness embed into the original Old expansion.

The new witness is initially a tagged-language, O-partite structure.
It is NOT automatically a normalized tagged expansion of an old-language
outer-partite structure; that descent is a separate remaining obligation.
No claim is made that the temporary O is globally U-semi-closed.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V W : Type v}

/-- The genuine local PictureProperty of an old D-partite picture is
EXACTLY sufficient to obtain an ordinary Ramsey arrow after naming
its parts and correctly tagging closure-relation symbols. No extra
closure hypothesis is needed for this colour-translation implication. -/
theorem taggedArrow_of_pictureProperty
    (rules : ClosureDescription L)
    (A : RelStructure L Q) (Old : System L P V)
    (alpha : Q ↪ P) (O : System L P W)
    (Color : Type*)
    (hPicture : Partite.PictureProperty A Old alpha O Color) :
    StructuralRamsey.Arrow
      (RelStructure.expandTaggedClosureParts rules A alpha)
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part)
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      Color := by
  let toTag :
      Partite.ProjectedEmbedding A O alpha →
        RelStructure.Embedding
          (RelStructure.expandTaggedClosureParts rules A alpha)
          (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part) :=
    fun e => e.val.expandTaggedClosureParts alpha O.part e.property
  intro chi
  obtain ⟨f, hf⟩ := hPicture (fun e => chi (toTag e))
  let fTag : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part)
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part) :=
    f.toEmbedding.expandTaggedClosureParts Old.part O.part f.map_part
  refine ⟨fTag, ?_⟩
  intro e1 e2
  let a1 : Partite.ProjectedEmbedding A Old alpha :=
    ⟨e1.forgetTaggedClosureParts, e1.tagged_preserves_part⟩
  let a2 : Partite.ProjectedEmbedding A Old alpha :=
    ⟨e2.forgetTaggedClosureParts, e2.tagged_preserves_part⟩
  have h1 : fTag.comp e1 = toTag (a1.comp f) := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have h2 : fTag.comp e2 = toTag (a2.comp f) := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  calc
    chi (fTag.comp e1) = chi (toTag (a1.comp f)) := congrArg chi h1
    _ = chi (toTag (a2.comp f)) := hf a1 a2
    _ = chi (fTag.comp e2) := congrArg chi h2.symm

/-- The selected closed-profile condition in the old little Picture
implies the EXACT relative-A-copy hypothesis of the repaired
relative-copy lemma in the tagged language. This checks EVERY tagged
embedding A+ -> O+, not only designated letters or canonical lines. -/
theorem taggedRelativeCopies_of_selected
    (rules : ClosureDescription L)
    (A : RelStructure L Q) (Old : System L P V)
    (alpha : Q ↪ P) (O : System L P W)
    (hA : IsUClosed rules A)
    (hSelected : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      ∀ e : RelStructure.Embedding Test O.toRelStructure,
        (∀ x, O.part (e x) ∈ Set.range alpha) →
        IsUSubstructure rules O.toRelStructure (Set.range e))
    (e : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules A alpha)
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)) :
    IsUSubstructure (rules.withTaggedClosureParts P)
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      (Set.range e) := by
  let eOld : RelStructure.Embedding A O.toRelStructure :=
    e.forgetTaggedClosureParts
  have hSelectedParts (x : Q) :
      O.part (eOld x) ∈ Set.range alpha :=
    ⟨x, e.tagged_preserves_part x⟩
  have hOld : IsUSubstructure rules O.toRelStructure (Set.range eOld) :=
    hSelected A hA eOld hSelectedParts
  have hTag :=
    (isUSubstructure_iff_taggedParts rules O.toRelStructure O.part
      (Set.range eOld)).mp hOld
  exact hTag

/-- A complete ONE-STEP recursive application of the already checked
relative-copy Ramsey theorem in the correctly tagged language.
The temporarily conflicting little Picture O need only satisfy
the local PictureProperty and selected-profile relative closedness.

An actual projected A-copy in Old is needed to meet the nontrivial
A-embeds-in-B premise of the lower-level relative-copy theorem.
No global U-closedness of O or projection to the outer control
is assumed or inferred. -/
theorem taggedRepair_of_littlePicture
    (rules : ClosureDescription L)
    (A : RelStructure L Q) (Old : System L P V)
    (alpha : Q ↪ P) (O : System L P W)
    [Finite Q] [Finite V] [Finite W]
    (hA : IsUClosed rules A)
    (hOld : IsUClosed rules Old.toRelStructure)
    (aOld : Partite.ProjectedEmbedding A Old alpha)
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hPicture : Partite.PictureProperty A Old alpha O Color)
    (hSelected : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      ∀ e : RelStructure.Embedding Test O.toRelStructure,
        (∀ x, O.part (e x) ∈ Set.range alpha) →
        IsUSubstructure rules O.toRelStructure (Set.range e)) :
    ∃ (Y : Type v) (_ : Finite Y)
      (T : System (L.withTaggedClosureParts rules P) W Y),
      StructuralRamsey.Arrow
        (RelStructure.expandTaggedClosureParts rules A alpha)
        (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part)
        T.toRelStructure Color ∧
      IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure ∧
      IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
        T.toRelStructure
        (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
        T.part ∧
      (∀ {X : Type v}
        (Test : RelStructure (L.withTaggedClosureParts rules P) X),
        IsUClosed (rules.withTaggedClosureParts P) Test →
        IsUIrreducible (rules.withTaggedClosureParts P) Test →
        RelStructure.Embedding Test T.toRelStructure →
        Nonempty (RelStructure.Embedding Test
          (RelStructure.expandTaggedClosureParts rules
            Old.toRelStructure Old.part))) := by
  let ATag := RelStructure.expandTaggedClosureParts rules A alpha
  let BTag := RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part
  let OTag := RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part
  have hATag : IsUClosed (rules.withTaggedClosureParts P) ATag :=
    (isUClosed_iff_taggedParts rules A alpha).mp hA
  have hBTag : IsUClosed (rules.withTaggedClosureParts P) BTag :=
    (isUClosed_iff_taggedParts rules Old.toRelStructure Old.part).mp hOld
  let aTag : RelStructure.Embedding ATag BTag :=
    aOld.val.expandTaggedClosureParts alpha Old.part aOld.property
  have hCopies : ∀ e : RelStructure.Embedding ATag OTag,
      IsUSubstructure (rules.withTaggedClosureParts P) OTag (Set.range e) :=
    fun e => taggedRelativeCopies_of_selected rules A Old alpha O hA hSelected e
  have hArrow : StructuralRamsey.Arrow ATag BTag OTag Color :=
    taggedArrow_of_pictureProperty rules A Old alpha O Color hPicture
  exact closed_ramsey_of_relative_A_copies
    ATag BTag OTag hATag hBTag aTag hCopies Color hArrow

end StructuralRamsey.Partite.Induced

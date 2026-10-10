import PartiteConstruction.Ramsey.ClosureSemiClosedAttachment
import PartiteConstruction.Partite.Picture

/-! # The actual line-family little Picture property

For the unrestricted initial repair of Theorem 2.18, the intermediate
little Picture may be globally non-semi-closed. Its attachments must
use the EXACT canonical Hales--Jewett line family: arbitrary partite
embeddings into the semi-closed core need not have relatively U-closed
ranges. This module proves the ordinary local PictureProperty for the
line-indexed attachment itself, rather than silently replacing it with
the all-embeddings Picture construction.

The proof is the original copy-extends diagram: the canonical line
embedding agrees on the attaching support with the corresponding
old-picture copy, and Hales--Jewett makes their A-subcopies monochromatic.
The result supplies the local Ramsey property, not closedness of the
whole little Picture or the complete recursive repair.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V W I : Type v}

/-- The actual old-copy attachment over a *chosen* family of full partite
embeddings of the exact part restriction into the central core. -/
noncomputable def familyPicture
    (Old : System L P V) (alpha : Q ↪ P) (Core : System L Q W)
    (f : I → Partite.Embedding (Old.restrict alpha) Core) :
    System L P (RelStructure.Attachment.Vertex (Old.support alpha)
      (W := W) (I := I)) :=
  Partite.Attachment.attach Old (Old.support alpha) (Core.relabel alpha)
    (fun i => Partite.Picture.attachingMap Old alpha Core (f i))

/-- The copy indexed by i in the actual chosen-family attachment. -/
noncomputable def familyCopyEmbedding
    (Old : System L P V) (alpha : Q ↪ P) (Core : System L Q W)
    (f : I → Partite.Embedding (Old.restrict alpha) Core) (i : I) :
    Partite.Embedding Old (familyPicture Old alpha Core f) :=
  Partite.Attachment.copyEmbedding Old (Old.support alpha) (Core.relabel alpha)
    (fun j => Partite.Picture.attachingMap Old alpha Core (f j)) i

/-- An A-copy inside the central core becomes a projected A-copy of
the whole little Picture at the selected alpha profile. -/
noncomputable def familyCoreLetter
    (A : RelStructure L Q)
    (Old : System L P V) (alpha : Q ↪ P)
    (Core : System L Q W)
    (f : I → Partite.Embedding (Old.restrict alpha) Core)
    (e : Partite.Embedding (transversal A) Core) :
    Partite.ProjectedEmbedding A (familyPicture Old alpha Core f) alpha := by
  let c := Partite.Attachment.coreEmbedding Old (Old.support alpha)
    (Core.relabel alpha) (fun j => Partite.Picture.attachingMap Old alpha Core (f j))
  refine ⟨c.toEmbedding.comp e.toEmbedding, ?_⟩
  intro x
  change alpha (Core.part (e x)) = alpha x
  exact congrArg alpha (e.map_part x)

/-- The copy of Old indexed by i agrees with the central core on
EVERY selected A-copy. This uses only the actual attaching-map identity,
not any closure assumption. -/
theorem familyCopy_comp_restrict
    (A : RelStructure L Q)
    (Old : System L P V) (alpha : Q ↪ P)
    (Core : System L Q W)
    (f : I → Partite.Embedding (Old.restrict alpha) Core)
    (i : I) (e : Partite.ProjectedEmbedding A Old alpha) :
    e.comp (familyCopyEmbedding Old alpha Core f i) =
      familyCoreLetter A Old alpha Core f
        ((f i).comp (Partite.Picture.restrictEmbedding e)) := by
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro x
  exact Partite.Attachment.copy_extends Old (Old.support alpha)
    (Core.relabel alpha) (fun j => Partite.Picture.attachingMap Old alpha Core (f j))
    i ⟨e.val x, x, (e.property x).symm⟩

/-- A Ramsey family of attaching embeddings produces an actual
local Picture property. Only the selected family needs to be
monochromatic; no Ramsey property for arbitrary core embeddings
is assumed. -/
theorem familyPictureProperty
    (A : RelStructure L Q)
    (Old : System L P V) (alpha : Q ↪ P)
    (Core : System L Q W)
    (f : I → Partite.Embedding (Old.restrict alpha) Core)
    (Color : Type*)
    (hFamily :
      ∀ chi : Partite.Embedding (transversal A) Core → Color,
        ∃ i : I,
          ∀ a b : Partite.Embedding (transversal A) (Old.restrict alpha),
            chi ((f i).comp a) = chi ((f i).comp b)) :
    Partite.PictureProperty A Old alpha (familyPicture Old alpha Core f) Color := by
  intro chi
  obtain ⟨i, hi⟩ := hFamily (fun e => chi (familyCoreLetter A Old alpha Core f e))
  refine ⟨familyCopyEmbedding Old alpha Core f i, ?_⟩
  intro e1 e2
  rw [familyCopy_comp_restrict A Old alpha Core f i e1,
    familyCopy_comp_restrict A Old alpha Core f i e2]
  exact hi (Partite.Picture.restrictEmbedding e1)
    (Partite.Picture.restrictEmbedding e2)

/-- In particular, a semi-closed part restriction admits a finite
canonical LINE-indexed little Picture with the genuine local
PictureProperty. It is NOT asserted that the total little Picture is
semi-closed. The line-family ranges are the relatively closed ones
certified by semiClosed_partiteLemma_lines. -/
theorem semiClosed_familyPictureProperty
    {rules : ClosureDescription L}
    (A : RelStructure L Q)
    (Old : System L P V) (alpha : Q ↪ P)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hOld : IsUSemiClosed rules Old.toRelStructure)
    [Finite Q] [Finite V]
    (Color : Type*) [Fintype Color] :
    ∃ N : ℕ, 0 < N ∧
      Partite.PictureProperty A Old alpha
        (familyPicture Old alpha
          (power (Old.restrict alpha) N)
          (fun line : Line (Letter A (Old.restrict alpha)) N =>
            lineEmbedding hRestricted line)) Color := by
  have hR : IsUSemiClosed rules (Old.restrict alpha).toRelStructure :=
    hOld.induce_isUSemiClosed (Old.support alpha)
  obtain ⟨N, hN, _, _, hLine⟩ :=
    semiClosed_partiteLemma_lines (Old.restrict alpha) hRestricted hR Color
  refine ⟨N, hN, ?_⟩
  exact familyPictureProperty A Old alpha (power (Old.restrict alpha) N)
    (fun line : Line (Letter A (Old.restrict alpha)) N =>
      lineEmbedding hRestricted line) Color hLine

end StructuralRamsey.Partite.Induced

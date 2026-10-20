import PartiteConstruction.Functional.NativeTaggedRelativeWeakSideLocalization
import PartiteConstruction.Functional.EHNAttachmentDecompose

/-!
# Actual native one-copy functional HJ attachment: exact weak relative-U localization

The REAL binary functional attachment of an old B over the genuinely
function-CLOSED support S to a native core E is a FULL free amalgam
E *_(B.induce S) B with all maps part-preserving.

The checked native tagged relative U-irreducible source-side theorem
applies to this actual diagram. For an arbitrary literal weak test
Test of the complete native attachment, if its AMBIENT singleton-tagged
U-root structure is RELATIVELY U-IRREDUCIBLE, then the entire Test is
contained in the true core range or the true attached B-copy range.

No closure hull or new vertices, no incorrect free cover of arbitrary
two HJ lines, and no global EHN domain reflection. The conclusion is
source localization, NOT an arbitrary strict TARGET B-tree completion.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}}
variable {P V W : Type v}

/-- Native exact weak relative-U localization for one genuine
full-functional old-copy attachment.

The common attaching support is function-closed, but the
exact tested vertex subset Test is NOT required to be closed.
The relative U-test uses induced AMBIENT root/domain tags. -/
theorem unit_tagged_relativeIrreducible_weak_side
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (E : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) E)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hIrred : RelStructure.IsURelativelyIrreducible
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        ((UnitAttachD B S hS E f).splitOutputParts).toStructure.patternGraph).induce Test)) :
    (∀ z : Test,
      ∃ w : W, z.1 = unitCoreEmbedding B S hS E f w) ∨
    (∀ z : Test,
      ∃ b : V, z.1 = unitCopyEmbedding B S hS E f b) := by
  let inclusion : FunctionalPartite.Embedding (B.induce S hS) B := {
    toEmbedding := Structure.inclusion B.toStructure S hS
    map_part := fun _ => rfl
  }
  let core : FunctionalPartite.Embedding E (UnitAttachD B S hS E f) :=
    FunctionalPartite.Attachment.coreEmbedding
      B S hS E (fun _ : PUnit.{v+1} => f)
  let copy : FunctionalPartite.Embedding B (UnitAttachD B S hS E f) :=
    FunctionalPartite.Attachment.copyEmbedding
      B S hS E (fun _ : PUnit.{v+1} => f) PUnit.unit
  have hFree :
      Structure.IsFreeAmalgam
        f.toEmbedding inclusion.toEmbedding
        core.toEmbedding copy.toEmbedding := by
    exact unit_isFreeAmalgam_full B S hS E f
  exact nativeTagged_relativeIrreducible_weak_side
    (sL := f) (sR := inclusion)
    (iL := core) (iR := copy)
    hFree Test hIrred

/-- In a genuine native one-copy attachment, a weak test meeting
both exclusive source-side exteriors cannot be relatively
U-irreducible in its canonical singleton-tagged ambient language.

The positive side-localization theorem above is applied by
contradiction, with neither weak source side closed by fiat. -/
theorem unit_tagged_mixed_weak_not_relativeIrreducible
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (E : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) E)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (zCore : Test)
    (hNotCore : ¬ ∃ w : W, zCore.1 = unitCoreEmbedding B S hS E f w)
    (zCopy : Test)
    (hNotCopy : ¬ ∃ b : V, zCopy.1 = unitCopyEmbedding B S hS E f b) :
    ¬ RelStructure.IsURelativelyIrreducible
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        ((UnitAttachD B S hS E f).splitOutputParts).toStructure.patternGraph).induce Test) := by
  intro hIrred
  rcases unit_tagged_relativeIrreducible_weak_side
    B S hS E f Test hIrred with hLeft | hRight
  · exact hNotCore (hLeft zCore)
  · exact hNotCopy (hRight zCopy)

end StructuralRamsey.FunctionalPartite.Attachment


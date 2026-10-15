import PartiteConstruction.Functional.ClosedPullbackAnchorFactor
import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-!
# Exact canonical anchor in the native functional attachment

Specialise the full-functional pullback anchor factorisation to the
actual one-copy attachment used recursively by the published EHN
Hales--Jewett Picture. Its old stage is glued along a full
function-closed selected support, and the embedding of that support
into the current core factors through the fixed HJ power core.

For EVERY genuine function-closed test, not merely weak induced
tests, the actual source common separator embeds into the exact
closed intersection of the test's current core piece with that HJ
power core. The root's inclusion into the tested left side is this
embedding followed by the canonical closed intersection inclusion.

This is the geometric factorisation required in the fixed-anchor
strict relative TreeExtension induction. It does not construct the
old-copy relative B-tree witness and does not automatically transport
the older anchored partial completion to the new tested core.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W X : Type v}

/-- The actual selected-support functional attachment has its closed
test separator INSIDE the tested original HJ core.

It suffices that the selected support embedding `f` into the current
stage factor through the distinguished full original core embedding.
This factorisation holds by construction in `EHN.attachList`:
the attached support maps are `core.comp (maps i)`.

The returned anchor is a fully function-closed structure, not an
artificial weak substructure or a larger generated closure. -/
theorem closedTestPullback_common_in_original_core
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (OriginalCore : Structure L X)
    (coreIn : Structure.Embedding OriginalCore D.toStructure)
    (supportIn : Structure.Embedding (B.induce S hS).toStructure OriginalCore)
    (hFactor : ∀ s : S, f.toEmbedding s = coreIn (supportIn s))
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test) :
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Structure.Embedding pb.common (pb.left.induce T hT)),
      ∀ x : pb.Common,
        (Structure.inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x := by
  exact Structure.IsFreeAmalgam.EmbeddingPullback.common_factors_through_closed_anchor
    (unit_isFreeAmalgam_full B S hS D f)
    (Structure.inclusion (UnitAttachD B S hS D f).toStructure Test hTest)
    (closedTestPullback B S hS D f Test hTest)
    OriginalCore coreIn supportIn hFactor

end StructuralRamsey.FunctionalPartite.Attachment

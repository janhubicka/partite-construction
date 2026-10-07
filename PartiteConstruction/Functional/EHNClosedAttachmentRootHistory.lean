import PartiteConstruction.Functional.EHNAttachmentDecompose
import PartiteConstruction.Functional.FreeAmalgamPullback
import PartiteConstruction.Functional.TreeExtensionAutoHistoryGlue

/-! # The closed functional EHN attachment and its relative root witness

One binary EHN attachment is a full functional free amalgam.  A genuine
function-closed test of this attachment pulls back to a full free-amalgam
diagram of closed test substructures, including the common overlap.

The relative projected-history gluing theorem can be applied to this
*actual* diagram, with no surrogate weak induced substructures.  The only
remaining hypothesis is the geometric one: both proper sides must admit
relative strict-tree witnesses over the *same* completion of their overlap.

This isolates the substantive reducible-root step for a subsequent
generator-rank or closed-test induction.  In particular, the lemma below
does not assert existence of a common root tree from independent local
completion witnesses.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P V W VB : Type v}
variable {Base : Structure L VB}
variable (B : System L P V)
variable (S : Set V) (hS : B.toStructure.IsClosed S)
variable (D : System L P W)
variable (f : FunctionalPartite.Embedding (B.induce S hS) D)

/-- The canonical full free-amalgam pullback of a closed functional test
inside a binary EHN attachment.  Its three source components and their
embeddings are genuine function-language substructures. -/
noncomputable def closedTestPullback
    (Test : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test) :
    IsFreeAmalgam.EmbeddingPullback
      (unit_isFreeAmalgam_full B S hS D f)
      (Structure.inclusion
        (UnitAttachD B S hS D f).toStructure Test hTest) :=
  (unit_isFreeAmalgam_full B S hS D f).embeddingPullback
    (Structure.inclusion
      (UnitAttachD B S hS D f).toStructure Test hTest)

/-- Conditional mixed completion for the exact closed-test pullback of
one functional EHN binary attachment.

The two assumed relative witnesses have the canonical projected maps
on their respective closed sides.  The finite singleton history is
requested internally; this recovers projection compatibility through a
possibly noninjective completed overlap.  We return only the originally
requested histories. -/
theorem closedTest_treeCompletion_of_sharedRootHistories
    [Fintype P] [Nonempty P]
    (Test : Finset
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B S hS D f).toStructure.IsClosed
        (↑Test : Set _))
    (pSmall : ↥(↑Test : Set (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1}))) → P)
    (history : List (Set P))
    (hShared :
      let pb := closedTestPullback B S hS D f (↑Test : Set _) hTest
      ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
        TreeAmalgam Base G Start ∧
        HasTreeExtensionProjectedHistoryCompletion
          (Base := Base) (Start := Start)
          pb.toLeft q (pSmall ∘ pb.leftIn)
          (history ++ singletonProjectedHistory P) ∧
        HasTreeExtensionProjectedHistoryCompletion
          (Base := Base) (Start := Start)
          pb.toRight q (pSmall ∘ pb.rightIn)
          (history ++ singletonProjectedHistory P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ completed : ↥(↑Test : Set (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1}))) → Z,
        ((UnitAttachD B S hS D f).toStructure.induce
          (↑Test : Set _) hTest).IsHomomorphismEmbedding Target completed ∧
        (∀ K ∈ history, ∀ (x y : ↥(↑Test : Set (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))),
          completed x = completed y →
            (pSmall x ∈ K ↔ pSmall y ∈ K)) := by
  classical
  let pb := closedTestPullback B S hS D f (↑Test : Set _) hTest
  obtain ⟨G, Start, q, hTreeRoot, hLeft, hRight⟩ := hShared
  obtain ⟨Z, Target, hExt, completed, hf, hcompat, hroot, hHist⟩ :=
    LocallyClosedTreeCompletable.glueRelative_withAutomaticProjectedHistory
      (Base := Base) pb.free q pSmall history hLeft hRight
  exact ⟨Z, Target, hExt.toTree hTreeRoot, completed, hf, hHist⟩

end StructuralRamsey.FunctionalPartite.Attachment

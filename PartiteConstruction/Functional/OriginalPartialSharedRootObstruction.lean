import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue
import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-!
# Refuting an over-uniform strict functional mixed-root extension schema

The published Appendix A mixed case needs two strict original-2019
partial-function extensions over ONE common completed root.  The
verified source free-amalgam gluing theorem shows immediately that
such compatible extensions imply an ABSOLUTE strict B-tree
completion of the full closed test.

This contrapositive is a useful reusable formal obstruction interface:
once a full closed mixed source test is shown not to have any original
partial B-tree completion, no choice of a shared root completion
(Start, q) can rescue it. In particular the obstruction is not a
failure of fixing the original A-label map.

The actual graph 5-cycle witness and the extra rank/projection
certificates are tracked separately. These lemmas have no additional
root, irreducibility, size, or partite hypotheses; they are pure
consequences of the already verified original-partial gluing theorem.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB : Type v}

/-- Absence of a strict original-partial B-tree completion of the
whole FREE source amalgam rules out ANY pair of compatible relative
side completions, even with a freely chosen reducible target tree
and freely chosen, possibly noninjective, root map. -/
theorem IsFreeAmalgam.no_originalPartial_sharedRoot_of_no_completion
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (hBad : ¬ HasOriginalPartialTreeCompletion Base Whole) :
    ¬ ∃ (G : Type v) (Start : Structure L G) (q : H → G),
      TreeAmalgam Base G Start ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base sL q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base sR q := by
  rintro ⟨G, Start, q, hStart, hLeft, hRight⟩
  exact hBad (hfree.originalPartialTreeCompletion_glue_relative
    Base hStart q hLeft hRight)

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W VB : Type v}

/-- The exact native functional EHN closed-test version. A closed
source test that cannot original-partially map into a strict B-tree
has no pair of compatible relative completions of its two TRUE
function-closed pullback sides, regardless of Start or q.

This is the precise contradiction interface for a candidate
maximal mixed-root schema counterexample; no extra function-closure
vertices or total-fibre homomorphisms enter the statement. -/
theorem closedTest_no_originalPartial_sharedRoot_of_no_completion
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB)
    (hBad : ¬ HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B S hS D f).toStructure.induce Test hTest)) :
    let pb := closedTestPullback B S hS D f Test hTest
    ¬ ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
      TreeAmalgam Base G Start ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toLeft q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toRight q := by
  let pb := closedTestPullback B S hS D f Test hTest
  exact pb.free.no_originalPartial_sharedRoot_of_no_completion Base hBad

end StructuralRamsey.FunctionalPartite.Attachment

import PartiteConstruction.Functional.OutputPartSplitFreeAmalgam
import PartiteConstruction.Functional.NativePatternGraphFreeAmalgam2019
import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge
import PartiteConstruction.Ramsey.ClosureUIrreducibleEquivalence

/-!
# Genuine functional free attachments localize all relatively U-irreducible weak tests

For any genuine FULL multivalued native functional partite free
amalgam, its canonical per-output-part singletonized OLD
equality-pattern and full U-root tagged presentation is an
EXACT relational free amalgam on the SAME source vertices.

Every ambient canonical tagged singleton structure is U-CLOSED
and hence U-SEMI-CLOSED. The verified 2019 semi-closed weak-side
localization therefore applies to ANY exact weak tested S:
a relatively U-irreducible induced AMBIENT tagged test must lie
entirely on one of the two true full source sides.

In particular a literal mixed weak S meeting both exclusive
sides is never U-RELATIVELY irreducible. No S is enlarged
to its function closure, and no global EHN part projection is
assumed full at undefined function inputs.

This specializes the precise relative-U source induction,
not the unproved strict history-compatible target B-tree
completion or a claim about intrinsic IsUIrreducible.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v}
variable {H E F C : Type w}

/-- Exact relative-U weak source-side localization in the
canonical tagged presentation of a TRUE native full-functional
free attachment.

The same literal weak vertex set S, even if nonclosed,
lies entirely on one source side whenever its induced
ambient tagged singleton output-part structure is
RELATIVELY U-IRREDUCIBLE.

This uses the verified relative 2019 theorem; intrinsic
U-irreducibility is intentionally a distinct predicate. -/
theorem nativeTagged_relativeIrreducible_weak_side
    {Root : System L P H}
    {Left : System L P E}
    {Right : System L P F}
    {Whole : System L P C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (S : Set C)
    (hIrred : RelStructure.IsURelativelyIrreducible
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (Whole.splitOutputParts).toStructure.patternGraph).induce S)) :
    (∀ z : S, ∃ a : E, z.1 = iL a) ∨
    (∀ z : S, ∃ b : F, z.1 = iR b) := by
  have hSplit : Structure.IsFreeAmalgam
      sL.splitOutputParts.toEmbedding
      sR.splitOutputParts.toEmbedding
      iL.splitOutputParts.toEmbedding
      iR.splitOutputParts.toEmbedding :=
    hFree.splitOutputParts_of_partite
  have hTag :=
    hSplit.taggedPatternGraph
  have hRootClosed :
      RelStructure.IsUClosed
        (L.outputPartIndexed P).patternClosureRules
        (RelStructure.patternTagExpansion
          (Root.splitOutputParts).toStructure.patternGraph) :=
    RelStructure.patternTagExpansion_isUClosed
      (Root.splitOutputParts).toStructure
      Root.splitOutputParts_singletonValued
  have hLeftSemi :
      RelStructure.IsUSemiClosed
        (L.outputPartIndexed P).patternClosureRules
        (RelStructure.patternTagExpansion
          (Left.splitOutputParts).toStructure.patternGraph) :=
    (RelStructure.patternTagExpansion_isUClosed
      (Left.splitOutputParts).toStructure
      Left.splitOutputParts_singletonValued).isUSemiClosed
  have hRightSemi :
      RelStructure.IsUSemiClosed
        (L.outputPartIndexed P).patternClosureRules
        (RelStructure.patternTagExpansion
          (Right.splitOutputParts).toStructure.patternGraph) :=
    (RelStructure.patternTagExpansion_isUClosed
      (Right.splitOutputParts).toStructure
      Right.splitOutputParts_singletonValued).isUSemiClosed
  exact hTag.uRelativeIrreducible_weak_side
    hRootClosed hLeftSemi hRightSemi S hIrred

/-- Every genuinely MIXED exact weak vertex test meeting both
exclusive source sides is NOT relatively U-irreducible in
its induced AMBIENT canonical tagged singleton presentation.

The input S may omit arbitrary original multivalued outputs;
the formula does not claim the common weak root is itself closed. -/
theorem nativeTagged_mixed_weak_not_relativeIrreducible
    {Root : System L P H}
    {Left : System L P E}
    {Right : System L P F}
    {Whole : System L P C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (S : Set C)
    (zL : S) (hNotL : ¬ ∃ a : E, zL.1 = iL a)
    (zR : S) (hNotR : ¬ ∃ b : F, zR.1 = iR b) :
    ¬ RelStructure.IsURelativelyIrreducible
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (Whole.splitOutputParts).toStructure.patternGraph).induce S) := by
  intro hIrred
  rcases nativeTagged_relativeIrreducible_weak_side
      hFree S hIrred with hAllL | hAllR
  · exact hNotL (hAllL zL)
  · exact hNotR (hAllR zR)


/-- The special case relevant to the COORDINATED corrected
2019 homomorphism-embedding tests: if the exact induced ambient
tagged weak test is in fact U-CLOSED and intrinsically
U-IRREDUCIBLE, it also lies on one actual full source side.

This uses the already verified equivalence between intrinsic
and relative U-irreducibility on U-closed structures.
It does NOT make an arbitrary nonclosed weak test U-closed. -/
theorem nativeTagged_closedUIrreducible_weak_side
    {Root : System L P H}
    {Left : System L P E}
    {Right : System L P F}
    {Whole : System L P C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (S : Set C)
    (hClosed : RelStructure.IsUClosed
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (Whole.splitOutputParts).toStructure.patternGraph).induce S))
    (hIntrinsic : RelStructure.IsUIrreducible
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (Whole.splitOutputParts).toStructure.patternGraph).induce S)) :
    (∀ z : S, ∃ a : E, z.1 = iL a) ∨
    (∀ z : S, ∃ b : F, z.1 = iR b) := by
  exact nativeTagged_relativeIrreducible_weak_side hFree S
    ((hClosed.uIrreducible_iff_relative).mp hIntrinsic)

end StructuralRamsey.FunctionalPartite

import PartiteConstruction.Partite.NonInduced
import PartiteConstruction.Partite.InducedBased
import PartiteConstruction.Partite.Induced
import PartiteConstruction.Iterated.TreeCompletion
import PartiteConstruction.Functional.ClosedAttachmentDecompose
import PartiteConstruction.Functional.InitialTreeCompletion
import PartiteConstruction.Functional.EHNRootDichotomy
import PartiteConstruction.Functional.EHNStrongInduction
import PartiteConstruction.Functional.TreeExtension
import PartiteConstruction.Structure.UClosed

/-!
# Appendix A survey: axiom checks for previously unprinted marker endpoints

These are the 12 Lean declarations referenced by 11 green survey markers
whose names were not found among previously executed root-level
`#print axioms` targets at the survey's pinned baseline.

No proof implementation changes. Review the output with the existing
root Check*.lean CI and `scripts/check_axioms.py`.
-/

#print axioms StructuralRamsey.Partite.NonInduced.lineEmbedding
#print axioms StructuralRamsey.Partite.NonInduced.wordEmbedding
#print axioms StructuralRamsey.Partite.Induced.BasedOn
#print axioms StructuralRamsey.Partite.Induced.lineEmbedding
#print axioms StructuralRamsey.RelStructure.LocallyTreeCompletable
#print axioms StructuralRamsey.Partite.Closed.Attachment.full_decompose_named
#print axioms StructuralRamsey.FunctionalPartite.EHN.initial_tree
#print axioms StructuralRamsey.FunctionalPartite.closedRoot_embedding_or_decompose
#print axioms StructuralRamsey.Structure.IsEHNHomomorphismEmbedding.finite_free_induction_with_common
#print axioms StructuralRamsey.Structure.TreeExtension.replayFree
#print axioms StructuralRamsey.Structure.TreeExtension.mergeFree
#print axioms StructuralRamsey.Structure.embeddingEquivUClosed

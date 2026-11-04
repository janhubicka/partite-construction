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
import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Partite.InducedInitial
import PartiteConstruction.Functional.HalfClosedInitial
import PartiteConstruction.Functional.TreeExtensionWitness

/-!
# Appendix A survey: axiom checks for previously unprinted marker endpoints

These are the 23 Lean declarations referenced by 11 previously unprinted green markers\nand several previously partial multi-endpoint markers
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

-- Existing multi-endpoint green and partial markers whose companion names
-- lacked a directly matched qualified axiom print in the survey audit.
#print axioms StructuralRamsey.Structure.weakInduce
#print axioms StructuralRamsey.Partite.Induced.power
#print axioms StructuralRamsey.Partite.Induced.power_isPartiteOver
#print axioms StructuralRamsey.Partite.Induced.lineMap_rel_iff
#print axioms StructuralRamsey.Partite.Induced.Initial.picture_isPartiteOver
#print axioms StructuralRamsey.Partite.Induced.Initial.picture_covers
#print axioms StructuralRamsey.Partite.HalfClosed.Initial.copyEmbedding
#print axioms StructuralRamsey.Partite.HalfClosed.Initial.uTransversal
#print axioms StructuralRamsey.Partite.HalfClosed.Initial.isPartiteOver
#print axioms StructuralRamsey.Structure.HasTreeExtensionCompletion.glue_relative
#print axioms StructuralRamsey.Structure.HasCommonRootedCompletions.glue

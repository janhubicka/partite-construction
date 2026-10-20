import PartiteConstruction.Functional.NativeStageSplitCopies
import PartiteConstruction.Functional.NativeTaggedWeakPreimage
import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge

/-!
# The real finite functional HJ source stage admits exact ambient U-root tests

The genuine EHN.Stage.attachList builds one ACTUAL finite native
multivalued partite source stage T with full core and attached B-copy
embeddings. Its vertex set and function interpretation are unchanged.

For positive function arities, singletonizing T by its output part
and applying the checked 2019 canonical tagged equality-pattern
presentation gives an exact dictionary on EVERY literal vertex
subset Test: native function-closedness iff induced AMBIENT
tagged U-closedness.

Every genuine FULL split attached-copy embedding, restricted
to the literal inverse image of ANY weak Test, also induces
a FULL relational embedding on ALL ambient tagged domain,
output and complete-root U-closure relations. Hence
the already verified weak-substructure/free-amalgam source
geometry of the 2019 U-closed proof holds on the ACTUAL
finite functional Picture stage, with the SAME vertices.

No new surrogate Picture, weak-test closure hull, global
full EHN projection or arbitrary strict B-tree TARGET
root-completion property is being asserted.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}}
variable {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual native finite HJ stage carries the EXACT 2019
U-closed tagged induced weak-set correspondence and FULL
tagged weak-preimage embeddings for every one of its real
attached copies. Every native and tagged carrier is the same
set of original vertices; no closure/rank inflation.

This source-side result does NOT supply compatible strict
functional target B-tree profiles for nonclosed mixed roots. -/
theorem attachList_taggedUClosedWeakCopies
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (hPos : L.PositiveFuncArity)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I) :
    ∃ T : Stage K D,
      (∀ Test : Set T.Carrier,
        T.system.toStructure.IsClosed Test ↔
          RelStructure.IsUClosed
            (L.outputPartIndexed P).patternClosureRules
            ((RelStructure.patternTagExpansion
              (T.system.splitOutputParts).toStructure.patternGraph).induce
                Test)) ∧
      ∃ core : FunctionalPartite.Embedding
          E.system.splitOutputParts T.system.splitOutputParts,
        ∀ i ∈ xs,
          ∃ copy : FunctionalPartite.Embedding
              B.splitOutputParts T.system.splitOutputParts,
            (∀ x : S, copy x.1 =
              core ((maps i).splitOutputParts x)) ∧
            (∀ Test : Set T.Carrier,
              Nonempty (RelStructure.Embedding
                ((RelStructure.patternTagExpansion
                  (B.splitOutputParts).toStructure.patternGraph).induce
                    (copy.toEmbedding.toFun ⁻¹' Test))
                ((RelStructure.patternTagExpansion
                  (T.system.splitOutputParts).toStructure.patternGraph).induce
                    Test))) := by
  classical
  obtain ⟨T, core, hCopies⟩ :=
    attachList_splitCopies hK B hB hmB S hS E maps xs
  have hDictionary : ∀ Test : Set T.Carrier,
      T.system.toStructure.IsClosed Test ↔
        RelStructure.IsUClosed
          (L.outputPartIndexed P).patternClosureRules
          ((RelStructure.patternTagExpansion
            (T.system.splitOutputParts).toStructure.patternGraph).induce
              Test) := by
    intro Test
    exact T.system.isClosed_iff_outputPartTaggedInduce_isUClosed
      hPos Test
  refine ⟨T, hDictionary, core, ?_⟩
  intro i hi
  obtain ⟨copy, hCopy⟩ := hCopies i hi
  refine ⟨copy, hCopy, ?_⟩
  intro Test
  exact ⟨copy.toEmbedding.taggedPatternWeakPreimage Test⟩

end StructuralRamsey.FunctionalPartite.EHN

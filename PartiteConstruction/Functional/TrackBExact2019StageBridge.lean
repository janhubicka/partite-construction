import PartiteConstruction.Functional.NativeFiniteStageUClosedWeakDictionary
import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.NativeTaggedWeakFreeAmalgam2019
import PartiteConstruction.Functional.WholeMaskWholeWeakImageRank2019
import PartiteConstruction.Functional.WholeMaskExactWeakLocalProjection2019

/-!
# Track B: exact-stage correspondence with 2019 U-closed tests

This assembles existing genuine source-side theorems, without building
a surrogate Picture or closing a weak test.

There are two distinct source conventions: clipped weakInduce with
outputPartIndexed tagging, and whole-fibre Option(Set) wholeWeakInduce
with persistent ambient OLD domain masks. They are NOT interchangeable
for multivalued fibres partly retained by a weak set.

The new theorems use the first convention on actual native EHN stages.
The imports provide separate 2019 whole-fibre weak projections and ranks.
This does not prove strict full-functional mixed-root tree completion,
intrinsic-local completion transfer or class-level Ramseyness.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}}
variable {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- On the exact weak subset of an ACTUAL native stage, both closed-set
and minimal-generator predicates agree with the induced ambient
U-closure presentation. No closure of the tested carrier is taken.
This is the CLIPPED native/singleton-output-part dictionary. -/
theorem Stage.exactWeakUClosureAndGeneratorRank
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    (Test : Set T.Carrier) [Fintype Test] (n : ℕ) :
    (∀ Q : Set Test,
      (T.system.toStructure.weakInduce Test).IsClosed Q ↔
        IsUSubstructure (L.outputPartIndexed P).patternClosureRules
          ((patternTagExpansion
            (T.system.splitOutputParts).toStructure.patternGraph).induce
              Test) Q) ∧
    ((T.system.toStructure.weakInduce Test).GeneratedByAtMost n ↔
      USize (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (T.system.splitOutputParts).toStructure.patternGraph).induce
            Test) ≤ n) := by
  constructor
  · intro Q
    exact T.system.weakIsClosed_iff_outputTagged_isUSubstructure
      hPos Test Q
  · exact T.system.weakGeneratedByAtMost_iff_outputTaggedUSize_le
      hPos Test n

/-- The ACTUAL finite full-functional attachment list simultaneously
retains canonical tagged full core/copy maps and exact weak rank.
This is a source-side certificate, not a strict target-tree theorem. -/
theorem attachList_taggedUClosedWeakRankCopies
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
      (∀ (Test : Set T.Carrier) [Fintype Test] (n : ℕ),
        (T.system.toStructure.weakInduce Test).GeneratedByAtMost n ↔
          USize (L.outputPartIndexed P).patternClosureRules
            ((patternTagExpansion
              (T.system.splitOutputParts).toStructure.patternGraph).induce
                Test) ≤ n) ∧
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
  obtain ⟨T, hClosed, core, hCopies⟩ :=
    attachList_taggedUClosedWeakCopies
      hK B hB hmB hPos S hS E maps xs
  refine ⟨T, hClosed, ?_, core, hCopies⟩
  intro Test hFin n
  letI : Fintype Test := hFin
  exact (T.exactWeakUClosureAndGeneratorRank hPos Test n).2

end StructuralRamsey.FunctionalPartite.EHN

import PartiteConstruction.Functional.TrackBRealEHNWeakLineTags2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019
import PartiteConstruction.Functional.TrackBWholeFibreActualStages2019

/-!
# Track B: exact real-line weak tests, OLD tags and generator rank

This is a SAME-CARRIER source contract for the actual functional EHN
Hales--Jewett line construction. A real EHN stage supplies only its
weak projection, not a full ProjectionHom. Its HJ line is nevertheless
a full functional embedding, hence transports complete OLD/root tags
on the literal inverse image of any tested subset of the actual power.

On that SAME inverse-image set, whole-fibre Option(Set) weak generator
rank is measured by the AMBIENT 2019 complete-mask USize. The EHN weak
part projection cannot increase this minimum-generator rank.

The two tagged presentations in the conclusion are intentionally
distinct: split-output fresh-root tags for the full LINE embedding,
and whole-fibre ambient OLD masks for generator rank. This theorem
does NOT assert an isomorphism between these languages, a
coordinatewise tagged-power identity, or an intrinsic weak target
completion. No closure hull replaces the original test.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The exact source subset selected by a genuine weak Hales--Jewett
line in the ACTUAL EHN stage power, with no closure or vertex change. -/
def Stage.actualLineWeakTest
    (T : Stage K D)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N)) : Set T.Carrier :=
  ((Induced.weak_lineEmbedding T.isPartite.1 W).splitOutputParts.toEmbedding.toFun) ⁻¹' Test

/-- Combined 2019 source certificate on the LITERAL weak-line preimage:
a full split-output tagged line embedding, equality of genuine
whole-fibre weak generator rank with ambient complete-mask USize,
and monotonicity of USize for the actual weak EHN part projection.

The line map is full; the projection is only original source-defined.
No assertion identifies the two independent tagged languages. -/
theorem Stage.actualLineTaggedAndWholeRank
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N))
    [Fintype (T.actualLineWeakTest W Test)]
    [Fintype (Structure.imageSet T.system.part (T.actualLineWeakTest W Test))]
    (n : ℕ) :
    let S := T.actualLineWeakTest W Test
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce S)
      ((patternTagExpansion
        ((Induced.power T.system N).splitOutputParts).toStructure.patternGraph).induce Test)) ∧
    ((wholeWeakInduce T.system.toStructure.toNonemptyPartial S).GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
            T.system.part)).induce S) ≤ n) ∧
    (USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((D.toNonemptyPartial).wholeMaskPatternGraph
          (fun p : P => p))).induce
            (Structure.imageSet T.system.part S)) ≤
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
            T.system.part)).induce S)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact T.taggedWeakLinePreimage W Test
  · exact (T.exactWholeWeakUClosureAndGeneratorRank
      hPos (T.actualLineWeakTest W Test) n).2
  · exact T.inducedAmbientWholeMaskUSize_le
      hPos (T.actualLineWeakTest W Test)

/-- If the literal HJ weak-line preimage needs at most n generators
under WHOLE-fibre deletion, its exact EHN control image has ambient
2019 OLD USize at most n. This uses the same original vertex maps;
no full projection or test closure is assumed. -/
theorem Stage.actualLine_controlImageUSize_le_of_generated
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N))
    [Fintype (T.actualLineWeakTest W Test)]
    [Fintype (Structure.imageSet T.system.part (T.actualLineWeakTest W Test))]
    (n : ℕ)
    (hGen : (wholeWeakInduce T.system.toStructure.toNonemptyPartial
      (T.actualLineWeakTest W Test)).GeneratedByAtMost n) :
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((D.toNonemptyPartial).wholeMaskPatternGraph
          (fun p : P => p))).induce
            (Structure.imageSet T.system.part (T.actualLineWeakTest W Test))) ≤ n := by
  have h := T.actualLineTaggedAndWholeRank hPos W Test n
  exact le_trans h.2.2 (h.2.1).mp hGen

end StructuralRamsey.FunctionalPartite.EHN

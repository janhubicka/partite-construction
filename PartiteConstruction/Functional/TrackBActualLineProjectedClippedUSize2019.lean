import PartiteConstruction.Functional.TrackBOneWayWeakUSize2019
import PartiteConstruction.Functional.TrackBRealEHNWeakLineTags2019
import PartiteConstruction.Functional.TrackBWholeFibreActualStages2019

/-!
# Track B: real weak HJ lines control the exact projected clipped rank

This packages two independently validated interfaces on the SAME
literal inverse image of an actual Hales--Jewett line inside a genuine
native EHN Stage:

* the line is a FULL function embedding despite the stage's merely
  source-defined weak part projection, and hence lifts ambient OLD
  equality-pattern/fresh-tag weak tests on exact inverse images;
* an n-generated whole-fibre weak test on that literal preimage has
  whole-mask USize ≤ n, whose actual stage projection gives a clipped
  USize ≤ n on its exact control image.

The tags in the two displayed terms are DISTINCT canonical presentations.
No intrinsic weak-test H-completion or strict full-functional target
B-tree is constructed. This is the geometry/rank side, not Track C/D.
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

/-- Real HJ line, exact weak preimage, and exact EHN control IMAGE.
The line induces a full split-output OLD tagged embedding; separately,
any whole-fibre n-generator witness on the very SAME preimage implies
an n-generator clipped 2019 USize bound on the projected image.

The conclusion is conditional ONLY on that actual S being
n-generated in the whole-fibre convention. That premise is not
conflated with n vertex cardinality or clipped generation. -/
theorem Stage.actualWeakLine_taggedAnd_projectedClippedUSize
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N))
    [Fintype (((Induced.weak_lineEmbedding T.isPartite.1 W).splitOutputParts.toEmbedding.toFun) ⁻¹' Test)]
    [Fintype (Structure.imageSet T.system.part
      (((Induced.weak_lineEmbedding T.isPartite.1 W).splitOutputParts.toEmbedding.toFun) ⁻¹' Test))]
    (n : ℕ) :
    let e := (Induced.weak_lineEmbedding T.isPartite.1 W).splitOutputParts.toEmbedding
    let S := e.toFun ⁻¹' Test
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce S)
      ((patternTagExpansion
        ((Induced.power T.system N).splitOutputParts).toStructure.patternGraph).induce Test)) ∧
    ((wholeWeakInduce T.system.toStructure.toNonemptyPartial S).GeneratedByAtMost n →
      USize (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          ((transversal D).splitOutputParts).toStructure.patternGraph).induce
            (Structure.imageSet T.system.part S)) ≤ n) := by
  constructor
  · exact T.taggedWeakLinePreimage W Test
  · intro hGen
    let S : Set T.Carrier :=
      ((Induced.weak_lineEmbedding T.isPartite.1 W).splitOutputParts.toEmbedding.toFun) ⁻¹' Test
    have hSource :
        USize (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
              T.system.part)).induce S) ≤ n :=
      (T.exactWholeWeakUClosureAndGeneratorRank hPos S n).2.mp hGen
    exact T.exactProjectedClippedUSize_le_of_wholeSource hPos S n hSource

end StructuralRamsey.FunctionalPartite.EHN

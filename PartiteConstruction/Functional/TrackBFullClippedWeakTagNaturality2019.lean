import PartiteConstruction.Functional.TrackBFullCopyWholeWeakClosureImage2019
import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019
import PartiteConstruction.Functional.TrackBRealEHNWeakLineTags2019

/-!
# Appendix Track B: clipped 2019 U-closure naturality along full native maps

The corrected native survey retains surviving individual output values
under a weak cut. This CLIPPED weak semantics differs from whole-fibre
deletion on mixed multivalued cuts; the two ambient 2019 tagged
presentations must not be silently identified.

Nevertheless, for a GENUINELY FULL native function embedding e:B→C,
the original nonempty-defined Option(Set) translation also gives a
full embedding. Its exact weak-clipped preimage is again FULL, so the
newly verified full-embedding closure-image equality applies.
Transport through the separately verified CLIPPED native/2019 U-tagged
closure dictionary gives exact equality of output-part-split
UClosureHull images on the actual original source and target carriers.

This is proved once for arbitrary full functional partite embeddings,
then applied to (1) literal full attached B-copies of a finite EHN
Stage and (2) true Hales--Jewett line embeddings in native coordinate
powers under only a WEAK EHN part projection.

No equality between whole-mask and clipped OLD tagged languages;
no coordinatewise tagged relational power equation; no full EHN
projection and no H-valued class-local completion is asserted.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Every genuine FULL Option(Set) embedding preserves generated
closures exactly under the CLIPPED weak restriction along any target
Test and its literal source preimage. Domain bits are fully retained
on this exact embedding diagram; neither Test is closed by fiat. -/
theorem Embedding.clippedWeakPreimage_imageClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B)
    (Test : Set W) (Q : Set (e.toFun ⁻¹' Test)) :
    Structure.imageSet (restrictMap e.toFun Test)
      ((weakInduce A (e.toFun ⁻¹' Test)).functionClosure Q) =
    (weakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap e.toFun Test) Q) :=
  (e.weakRestrictToPreimage Test).image_functionClosure_eq Q

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V W : Type v} [Fintype P]

/-- On any exact target weak Test, a FULL native partite B-copy
preserves the original output-part-split CLIPPED 2019 UClosureHull
of every seed on the exact source preimage.

The two displayed ambient tagged systems come directly from the
actual native source and target; this is NOT a whole-mask theorem. -/
theorem System.fullEmbedding_outputTaggedUClosureHull_image_eq
    (B : System L P V) (C : System L P W)
    [Finite V] [Finite W]
    (e : FunctionalPartite.Embedding B C)
    (hPos : L.PositiveFuncArity)
    (Test : Set W)
    (Q : Set (e.toEmbedding.toFun ⁻¹' Test)) :
    let S := e.toEmbedding.toFun ⁻¹' Test
    let g := restrictMap e.toEmbedding.toFun Test
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q) =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (C.splitOutputParts).toStructure.patternGraph).induce Test)
      (Structure.imageSet g Q) := by
  let S : Set V := e.toEmbedding.toFun ⁻¹' Test
  let g : S → Test := restrictMap e.toEmbedding.toFun Test
  have hSource :
      (B.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q =
      UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q := by
    calc
      _ = ((B.toStructure.weakInduce S).toNonemptyPartial).functionClosure Q := by
        rw [Structure.toNonemptyPartial_weakInduce_commute]
      _ = (B.toStructure.weakInduce S).functionClosure Q :=
        (B.toStructure.weakInduce S).toNonemptyPartial_functionClosure Q
      _ = _ := B.weakFunctionClosure_eq_outputTaggedUClosureHull hPos S Q
  have hTarget :
      (C.toStructure.toNonemptyPartial.weakInduce Test).functionClosure
        (Structure.imageSet g Q) =
      UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (C.splitOutputParts).toStructure.patternGraph).induce Test)
        (Structure.imageSet g Q) := by
    calc
      _ = ((C.toStructure.weakInduce Test).toNonemptyPartial).functionClosure
          (Structure.imageSet g Q) := by
        rw [Structure.toNonemptyPartial_weakInduce_commute]
      _ = (C.toStructure.weakInduce Test).functionClosure
          (Structure.imageSet g Q) :=
        (C.toStructure.weakInduce Test).toNonemptyPartial_functionClosure
          (Structure.imageSet g Q)
      _ = _ := C.weakFunctionClosure_eq_outputTaggedUClosureHull hPos Test
        (Structure.imageSet g Q)
  have hFull :
      Structure.imageSet g
        ((B.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q) =
      (C.toStructure.toNonemptyPartial.weakInduce Test).functionClosure
        (Structure.imageSet g Q) :=
    (e.toEmbedding.toNonemptyPartial).clippedWeakPreimage_imageClosure_eq Test Q
  calc
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q)
        = Structure.imageSet g
          ((B.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q) :=
          congrArg (Structure.imageSet g) hSource.symm
    _ = (C.toStructure.toNonemptyPartial.weakInduce Test).functionClosure
          (Structure.imageSet g Q) := hFull
    _ = UClosureHull (L.outputPartIndexed P).patternClosureRules
          ((patternTagExpansion
            (C.splitOutputParts).toStructure.patternGraph).induce Test)
          (Structure.imageSet g Q) := hTarget

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Literal full attached-copy maps in the TRUE finite EHN Stage
preserve 2019 CLIPPED tagged source closure images on every exact
weak target Test and source preimage. No whole-fibre substitution. -/
theorem Stage.fullCopy_outputTaggedUClosureHull_image_eq
    (T : Stage K D)
    (B : System L P V) [Finite V]
    (copy : FunctionalPartite.Embedding B T.system)
    (hPos : L.PositiveFuncArity)
    (Test : Set T.Carrier)
    (Q : Set (copy.toEmbedding.toFun ⁻¹' Test)) :
    let S := copy.toEmbedding.toFun ⁻¹' Test
    let g := restrictMap copy.toEmbedding.toFun Test
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q) =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce Test)
      (Structure.imageSet g Q) := by
  exact B.fullEmbedding_outputTaggedUClosureHull_image_eq
    T.system copy hPos Test Q

/-- The ACTUAL weak HJ line of an EHN Stage is itself FULL native:
hence it preserves the CLIPPED output-part-split 2019 UClosureHull
images on exact source/target weak tests, despite the weak projection. -/
theorem Stage.actualWeakLine_outputTaggedUClosureHull_image_eq
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N))
    (Q : Set (((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) ⁻¹' Test)) :
    let S := ((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) ⁻¹' Test
    let g := restrictMap ((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) Test
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q) =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        ((Induced.power T.system N).splitOutputParts).toStructure.patternGraph).induce Test)
      (Structure.imageSet g Q) := by
  exact T.system.fullEmbedding_outputTaggedUClosureHull_image_eq
    (Induced.power T.system N)
    (Induced.weak_lineEmbedding T.isPartite.1 W) hPos Test Q

end StructuralRamsey.FunctionalPartite.EHN

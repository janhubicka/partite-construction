import PartiteConstruction.Functional.TrackBFullCopyWholeWeakClosureImage2019
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.NativeWholePartClosure

/-!
# Track B: canonical 2019 complete-mask U-closure naturality on ACTUAL copies

The corrected 2019 partial-function proof computes exact-source weak
generator closure using the AMBIENT complete OLD domain/output/root mask
presentation, not a coordinatewise relational power and not a clipped
multivalued approximation.

The independently checked exact-carrier whole-fibre U-closure
dictionaries agree with the genuine Option(Set) weak closure for the
actual source B and target EHN Stage T. A FULL native attached-copy
map B→T restricts to a FULL genuine-partial weak embedding on the exact
preimage of ANY target Test. The generated closure of every seed Q on
this exact preimage therefore maps ONTO the generated closure of its
image in the target Test.

Combining these checked maps yields equality of canonical 2019
complete-mask UClosureHull images on the original copy vertex maps.
This is stronger than general original EHN weak-projection transport,
where only ONE-WAY image inclusion (merged Track B #654) is true.

No equality of the tagged relational languages, global full EHN
projection, arbitrary H-valued target completion, or closure of
the weak tested carrier is asserted.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Every FULL attached B-copy of an ACTUAL finite EHN Stage preserves
the 2019 OLD complete-mask generated closure of EVERY seed on the
literal exact weak source preimage. The target closure is computed in
the AMBIENT tagged Stage induced on the original unclosed Test, not
in an artificially closed copy or target hull. -/
theorem Stage.fullCopy_wholeMaskUClosureHull_image_eq
    (T : Stage K D)
    (B : System L P V) [Finite V]
    (copy : FunctionalPartite.Embedding B T.system)
    (hPos : L.PositiveFuncArity)
    (Test : Set T.Carrier)
    (Q : Set (copy.toEmbedding.toFun ⁻¹' Test)) :
    let S := copy.toEmbedding.toFun ⁻¹' Test
    let g := restrictMap copy.toEmbedding.toFun Test
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q) =
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
          T.system.part)).induce Test)
      (Structure.imageSet g Q) := by
  let S : Set V := copy.toEmbedding.toFun ⁻¹' Test
  let g : S → Test := restrictMap copy.toEmbedding.toFun Test
  have hSource :
      (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q :=
    B.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      B.part hPos B.toNonemptyPartial_fibreTransversal S Q
  have hTarget :
      (wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce Test)
        (Structure.imageSet g Q) :=
    T.system.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      T.system.part hPos T.system.toNonemptyPartial_fibreTransversal Test
      (Structure.imageSet g Q)
  have hFull :
      Structure.imageSet g
        ((wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q) =
      (wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) :=
    T.fullCopy_wholeWeakPreimage_imageClosure_eq B copy Test Q
  calc
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q)
        = Structure.imageSet g
            ((wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q) :=
          congrArg (Structure.imageSet g) hSource.symm
    _ = (wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).functionClosure
          (Structure.imageSet g Q) := hFull
    _ = UClosureHull (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
              T.system.part)).induce Test)
          (Structure.imageSet g Q) := hTarget

end StructuralRamsey.FunctionalPartite.EHN

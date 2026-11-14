import PartiteConstruction.Functional.TrackBFullCopyWholeWeakClosureImage2019
import PartiteConstruction.Functional.TrackBRealEHNWeakLineTags2019
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.NativeWholePartClosure

/-!
# Appendix Track B: complete 2019 U-closure images on REAL HJ lines

Every genuine weak-projection Hales--Jewett line map is FULL native
functional, even though its underlying part projection is only EHN weak.
The merged full-embedding weak-preimage theorem therefore proves EXACT
equality of WHOLE-fibre generated closure images along the literal line.

Translate source and target via the separately checked ambient 2019
complete-mask U-closure dictionaries. The resulting two OLD tagged
relations are independently built from the ORIGINAL native source and
actual coordinate power, on the SAME exact weak source preimage and
target Test. No assumption that canonical tagging commutes with
coordinatewise relational power is introduced.

The theorem also specializes to a real finite EHN Stage, using its
stored WeaklyPartiteOver invariant, not ProjectionHom. This remains a
source-side naturality certificate, not an H-valued completion theorem
or a strict functional mixed-root B-tree target.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]

/-- On the EXACT weak inverse image of an ACTUAL full HJ line, the
2019 complete-mask UClosureHull image is equal to the corresponding
2019 UClosureHull inside the actual native power's exact test.

The native power and both OLD tag structures have the same original
vertex carriers as in the functional Picture construction. -/
theorem weakLine_wholeMaskUClosureHull_image_eq
    (A : Structure L P) (B : System L P V) [Finite V]
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N))
    (Q : Set (((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test)) :
    let S := ((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test
    let g := restrictMap ((weak_lineEmbedding hB W).toEmbedding.toFun) Test
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q) =
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (((power B N).toStructure.toNonemptyPartial).wholeMaskPatternGraph
          (power B N).part)).induce Test)
      (Structure.imageSet g Q) := by
  let S : Set V := ((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test
  let g : S → Test :=
    restrictMap ((weak_lineEmbedding hB W).toEmbedding.toFun) Test
  have hSource :
      (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q :=
    B.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      B.part hPos B.toNonemptyPartial_fibreTransversal S Q
  have hTarget :
      (wholeWeakInduce (power B N).toStructure.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (((power B N).toStructure.toNonemptyPartial).wholeMaskPatternGraph
            (power B N).part)).induce Test)
        (Structure.imageSet g Q) :=
    (power B N).toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      (power B N).part hPos (power B N).toNonemptyPartial_fibreTransversal Test
      (Structure.imageSet g Q)
  have hFull :
      Structure.imageSet g
        ((wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q) =
      (wholeWeakInduce (power B N).toStructure.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) :=
    weakLine_wholeWeakPreimage_imageClosure_eq A B hB W Test Q
  calc
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q)
        = Structure.imageSet g
            ((wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q) :=
          congrArg (Structure.imageSet g) hSource.symm
    _ = (wholeWeakInduce (power B N).toStructure.toNonemptyPartial Test).functionClosure
          (Structure.imageSet g Q) := hFull
    _ = UClosureHull (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            (((power B N).toStructure.toNonemptyPartial).wholeMaskPatternGraph
              (power B N).part)).induce Test)
          (Structure.imageSet g Q) := hTarget

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The literal weak line maps of an actual finite EHN Stage have
complete-mask 2019 UClosureHull image EQUALITY on every exact weak
power test. Uses only the stored EHN weak part projection. -/
theorem Stage.actualWeakLine_wholeMaskUClosureHull_image_eq
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N))
    (Q : Set (((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) ⁻¹' Test)) :
    let S := ((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) ⁻¹' Test
    let g := restrictMap ((Induced.weak_lineEmbedding T.isPartite.1 W).toEmbedding.toFun) Test
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce S) Q) =
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (((Induced.power T.system N).toStructure.toNonemptyPartial).wholeMaskPatternGraph
          (Induced.power T.system N).part)).induce Test)
      (Structure.imageSet g Q) := by
  exact Induced.weakLine_wholeMaskUClosureHull_image_eq
    D T.system T.isPartite.1 hPos W Test Q

end StructuralRamsey.FunctionalPartite.EHN

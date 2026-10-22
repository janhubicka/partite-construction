import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Structure.PartialSetFunctionsClosure

/-!
# Exact whole-weak USize does not increase under projected images

The proof uses the genuine source-defined partial homomorphism on the
WHOLE-FIBRE weak restriction, which is surjective onto the exact image
carrier. Its images of finite generators still generate the target.
The already checked canonical complete-mask USize dictionary transports
that inequality to the 2019 relational closure presentation.

Neither source nor target image carrier is enlarged to an ambient
function closure. In particular we never count hull vertices in place
of the size of a minimal generating subset.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- USize of the induced AMBIENT complete-mask tag graph on the exact
weak image f[S] is bounded by any bound for the induced AMBIENT graph
on S. The map need only preserve source-defined partial applications;
it need not reflect undefined operations, nor be injective. -/
theorem IsOriginalPartialHomomorphism.inducedAmbientWholeMaskUSize_le_of_le
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    [Finite V] [Finite W]
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (partA : V → P) (partB : W → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hPos : L.PositiveFuncArity)
    (S : Set V) (n : ℕ)
    (hRank : USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)).induce S) ≤ n) :
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (B.wholeMaskPatternGraph partB)).induce
        (Structure.imageSet f S)) ≤ n := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (Structure.imageSet f S) :=
    Fintype.ofFinite (Structure.imageSet f S)
  have hGen : (wholeWeakInduce A S).GeneratedByAtMost n :=
    (A.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      partA hPos hTransA S n).mpr hRank
  have hGenB :
      (wholeWeakInduce B (Structure.imageSet f S)).GeneratedByAtMost n :=
    hf.wholeWeakImage_generatedByAtMost S hGen
  exact
    (B.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      partB hPos hTransB (Structure.imageSet f S) n).mp hGenB

/-- The exact 2019 U-generator size of the image is no larger than the
source U-generator size, even if f identifies different source vertices
or some ambient function applications do not survive the weak cut. -/
theorem IsOriginalPartialHomomorphism.inducedAmbientWholeMaskUSize_le
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    [Finite V] [Finite W]
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (partA : V → P) (partB : W → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hPos : L.PositiveFuncArity) (S : Set V) :
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (B.wholeMaskPatternGraph partB)).induce
        (Structure.imageSet f S)) ≤
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)).induce S) :=
  hf.inducedAmbientWholeMaskUSize_le_of_le
    partA partB hTransA hTransB hPos S _ (le_refl _)

end StructuralRamsey.PartialSetStructure

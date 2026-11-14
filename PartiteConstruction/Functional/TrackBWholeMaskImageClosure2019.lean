import PartiteConstruction.Functional.WholeMaskWholeWeakImageRank2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019

/-!
# Track B: exact-image functoriality of ambient 2019 whole-mask U-closures

The previously checked original source-defined partial map preserves complete
defined output fibres on EVERY exact whole-weak source test S and maps it onto
the literal image f''S. Therefore it transports generated vertex closures,
not merely minimum-generator USize bounds.

Translate source and target through the INDEPENDENT canonical complete-mask
closure dictionaries. The result compares whole-mask UClosureHull with
whole-mask UClosureHull (a strengthening of the whole-to-CLIPPED conclusion
in TrackBExactWeakImageClosure2019), without requiring that the exact tested
weak carrier or its image be function-closed.

A source-defined map need not reflect undefined function applications;
this theorem is NOT a full OLD/tagged relational embedding, does not assert
tagged-language equality, and does not construct a relative H-completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- Exact-image transport of each ambient whole-mask 2019 closure hull.
The two structures may have different carrier types and part maps; a
source-defined partial homomorphism is enough to transport GENERATED
vertices. No injectivity, domain reflection, or closed-test premise. -/
theorem IsOriginalPartialHomomorphism.inducedAmbientWholeMaskUClosureHull_image_subset
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    [Finite V] [Finite W]
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (partA : V → P) (partB : W → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hPos : L.PositiveFuncArity)
    (S : Set V) (Q : Set S) :
    Structure.imageSet (wholeWeakImageMap f S)
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)).induce S) Q) ⊆
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (B.wholeMaskPatternGraph partB)).induce
        (Structure.imageSet f S))
      (Structure.imageSet (wholeWeakImageMap f S) Q) := by
  let I : Set W := Structure.imageSet f S
  let g : S → I := wholeWeakImageMap f S
  let G : Set I := Structure.imageSet g Q
  have hSource :
      (wholeWeakInduce A S).functionClosure Q =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)).induce S) Q :=
    A.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      partA hPos hTransA S Q
  have hTarget :
      (wholeWeakInduce B I).functionClosure G =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (B.wholeMaskPatternGraph partB)).induce I) G :=
    B.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      partB hPos hTransB I G
  have hMap :
      Structure.imageSet g
        ((wholeWeakInduce A S).functionClosure Q) ⊆
        (wholeWeakInduce B I).functionClosure G :=
    (hf.wholeWeakImage S).image_functionClosure_subset Q
  calc
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)).induce S) Q)
        = Structure.imageSet g
            ((wholeWeakInduce A S).functionClosure Q) :=
          congrArg (Structure.imageSet g) hSource.symm
    _ ⊆ (wholeWeakInduce B I).functionClosure G := hMap
    _ = UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion (B.wholeMaskPatternGraph partB)).induce I) G :=
      hTarget

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- At every actual finite EHN Stage, the SAME original weak part
projection carries each whole-mask tagged U-closure on any literal weak
test S into the whole-mask tagged U-closure on the EXACT image part''S.
This strengthens the separately verified whole-to-clipped inclusion,
without changing either test or imposing a full ProjectionHom. -/
theorem Stage.exactImageWholeMaskUClosureHull_subset_wholeMask
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) (Q : Set S) :
    Structure.imageSet (wholeWeakImageMap T.system.part S)
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce S) Q) ⊆
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (D.toNonemptyPartial.wholeMaskPatternGraph (fun p : P => p))).induce
          (Structure.imageSet T.system.part S))
      (Structure.imageSet (wholeWeakImageMap T.system.part S) Q) := by
  have hf : IsOriginalPartialHomomorphism
      T.system.toStructure.toNonemptyPartial D.toNonemptyPartial T.system.part :=
    T.system.weaklyPartite_toNonemptyPartial_originalHom D T.isPartite
  have hTransSource : FibreTransversal
      T.system.toStructure.toNonemptyPartial T.system.part :=
    T.system.toNonemptyPartial_fibreTransversal
  have hTransTarget : FibreTransversal
      D.toNonemptyPartial (fun p : P => p) :=
    (transversal D).toNonemptyPartial_fibreTransversal
  exact hf.inducedAmbientWholeMaskUClosureHull_image_subset
    T.system.part (fun p : P => p)
    hTransSource hTransTarget hPos S Q

end StructuralRamsey.FunctionalPartite.EHN

import PartiteConstruction.Functional.TrackBOneWayClosureHull2019
import PartiteConstruction.Functional.TrackBOneWayWeakUSize2019
import PartiteConstruction.Functional.EHNLineOnlyProjectedCover

/-!
# Appendix Track B: source-side U-size contract for the ACTUAL line-only Picture

The original native functional EHN Picture attaches full copies of the
preceding stage only along true Hales--Jewett LINE maps. The verified
line-only construction supplies both PictureProperty and projected
irreducible B-cover on one genuine finite stage C.

On precisely THAT C (not an independently constructed surrogate),
every exact source weak S has the whole-fibre-to-clipped canonical
2019 relative closure-hull inclusion, and every exact weak source S
of whole-mask USize <= n has an exact projected control image of
clipped USize <= n.

This is a reusable source bookkeeping certificate. No bound is
assumed on the cardinality of the ambient closure of S; no
canonical tagged-language isomorphism, intrinsically weak full
embedding, class H-valued local completion, or strict functional
mixed-root B-tree conclusion is introduced.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- One ACTUAL native line-only Picture stage C simultaneously has
the old verified Ramsey canonicalization, projected B-coverage,
and both exact S-source comparison contracts from Track B.

The closure comparison is for ANY seed Q ⊆ the SAME literal S,
inside the two distinct ambient 2019 tagged sources induced on S.
The generator-rank implication is for the same S and its precise
part image, not their respective ambient closures. -/
theorem pictureLemma_lines_projectedCover_withExactSourceUSize
    [Fintype P]
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (Base : Structure L V)
    (Old : Stage K D) (hOld : Old.ProjectedCover Base)
    (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] (hPos : L.PositiveFuncArity) :
    ∃ C : Stage K D,
      C.ProjectedCover Base ∧
      PictureProperty A Old C α κ ∧
      (∀ (S : Set C.Carrier) (Q : Set S),
        UClosureHull (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            (C.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
              C.system.part)).induce S) Q ⊆
        UClosureHull (L.outputPartIndexed P).patternClosureRules
          ((patternTagExpansion
            (C.system.splitOutputParts).toStructure.patternGraph).induce S) Q) ∧
      (∀ (S : Set C.Carrier) [Fintype S]
        [Fintype (Structure.imageSet C.system.part S)]
        (n : ℕ),
        USize (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            (C.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
              C.system.part)).induce S) ≤ n →
        USize (L.outputPartIndexed P).patternClosureRules
          ((patternTagExpansion
            ((transversal D).splitOutputParts).toStructure.patternGraph).induce
              (Structure.imageSet C.system.part S)) ≤ n) := by
  classical
  obtain ⟨C, hCover, hPic⟩ :=
    pictureLemma_lines_projectedCover hK A hA Base Old hOld α κ
  refine ⟨C, hCover, hPic, ?_, ?_⟩
  · intro S Q
    exact C.system.wholeMaskUClosureHull_subset_clipped hPos S Q
  · intro S hFinS hFinImage n hSource
    letI : Fintype S := hFinS
    letI : Fintype (Structure.imageSet C.system.part S) := hFinImage
    exact C.exactProjectedClippedUSize_le_of_wholeSource
      hPos S n hSource

end StructuralRamsey.FunctionalPartite.EHN

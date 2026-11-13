import PartiteConstruction.Functional.TrackBOneWayWeakUSize2019
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.NativePartialClosure

/-!
# Track B: relative closure-hull comparison on arbitrary exact weak tests

The source-defined identity map from whole-fibre weak restriction to
clipped weak restriction transports not just minimum-generator bounds,
but every generated closure from EVERY initial seed Q inside a literal
weak carrier S. On the SAME original S, whole-fibre closure is
contained in clipped closure.

The two canonical ambient 2019 tag presentations are NOT declared
isomorphic. Instead their distinct UClosureHull predicates are
compared through the separately verified literal weak-source
dictionaries, with no test replacement or ambient closure of S.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- For every seed Q on the SAME exact S, closure under whole-fibre
retained applications is contained in closure under clipped
applications. The map is source-defined, not domain-reflecting. -/
theorem wholeWeakFunctionClosure_subset_clipped
    (A : PartialSetStructure L V) (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).functionClosure Q ⊆
      (weakInduce A S).functionClosure Q := by
  simpa only [Set.image_id] using
    (wholeWeakInduce_to_clipped_originalPartial A S).image_functionClosure_subset Q

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]

/-- The SAME-TEST, SAME-SEED comparison of the two canonical
2019 ambient U-closure presentations, valid for every weak S and
Q ⊆ S. Whole-mask/whole-fibre generated closure is contained in
output-part-indexed/clipped generated closure.

This is not an identification of closure RULES or tagged languages,
nor a converse implication on arbitrary multivalued weak tests. -/
theorem System.wholeMaskUClosureHull_subset_clipped
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (Q : Set S) :
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q ⊆
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) Q := by
  have hInclusion :
      (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q ⊆
        (B.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q :=
    B.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_subset_clipped S Q
  have hWhole :=
    B.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      B.part hPos B.toNonemptyPartial_fibreTransversal S Q
  have hClipped :=
    B.weakFunctionClosure_eq_outputTaggedUClosureHull hPos S Q
  calc
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q
        = (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q :=
          hWhole.symm
    _ ⊆ (B.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q :=
      hInclusion
    _ = ((B.toStructure.weakInduce S).toNonemptyPartial).functionClosure Q := by
      rw [Structure.toNonemptyPartial_weakInduce_commute]
    _ = (B.toStructure.weakInduce S).functionClosure Q :=
      (B.toStructure.weakInduce S).toNonemptyPartial_functionClosure Q
    _ = UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) Q :=
      hClipped

end StructuralRamsey.FunctionalPartite

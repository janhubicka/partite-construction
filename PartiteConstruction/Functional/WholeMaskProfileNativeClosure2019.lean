import PartiteConstruction.Functional.WholeMaskClosednessDictionary2019
import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-!
# A 2019 generated-closure profile is literally a functional closure

The verified coordinated 2019 two-pass sparsening proof records the
CLOSED hull of every weak gluing root by an auxiliary relation.
For genuine partial Option(Set)-valued functions with transversal
outputs and positive input arities, this closed hull in the canonical
whole-mask U-language is not an invented new object: it equals the
ACTUAL vertex closure under the original partial functions.

Proof: both closures are defined as the least subset closed under
the same operations. The verified whole-mask closed-substructure
dictionary equates their predicates on EVERY subset, not merely
on the tested root. Thus their intersections coincide.

This is the missing native semantic crosswalk for the 2019
generated-closure profile method. The weak test S is not enlarged:
the statement identifies the generated target-side boundary only.
Defined-empty outputs introduce no extra closure vertices.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- The 2019 U-closure hull in the canonical whole-mask tagged source
is EXACTLY the original function-closed hull on the original vertex
carrier. This is about a generated TARGET-SIDE boundary, not the
intrinsic closure of an induced weak test. -/
theorem wholeMaskUClosureHull_eq_functionClosure
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) :
    UClosureHull (L.wholeMaskClosureRules P)
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) S =
      A.functionClosure S := by
  let Tagged := wholeMaskTagExpansion (A.wholeMaskPatternGraph part)
  let rules := L.wholeMaskClosureRules P
  have hClosed (T : Set V) :
      A.IsClosed T ↔ IsUSubstructure rules Tagged T :=
    A.isClosed_iff_wholeMaskTagged_isUSubstructure
      part hPos hTrans T
  apply Set.Subset.antisymm
  · exact UClosureHull_minimal rules Tagged
      ((hClosed (A.functionClosure S)).mp
        (A.functionClosure_isClosed S))
      (A.subset_functionClosure S)
  · exact A.functionClosure_least
      ((hClosed (UClosureHull rules Tagged S)).mpr
        (UClosureHull_isUSubstructure rules Tagged S))
      (subset_UClosureHull rules Tagged S)

/-- Thus the closed boundary of a tuple recorded by the 2019
generated profile is genuinely closed under the original
set-valued PARTIAL operations. No source test or size bound
changes in this passage. -/
theorem wholeMaskGeneratedProfileHull_isClosed
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set V) :
    A.IsClosed
      (UClosureHull (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) S) := by
  rw [A.wholeMaskUClosureHull_eq_functionClosure part hPos hTrans S]
  exact A.functionClosure_isClosed S

end StructuralRamsey.PartialSetStructure

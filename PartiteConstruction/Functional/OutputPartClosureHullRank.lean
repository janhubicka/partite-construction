import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge
import PartiteConstruction.Functional.ClosedGeneratorRank

/-!
# Exact closure hull and finite generator size under output-part singletonization

A real transversal functional partite System B, with arbitrary
multivalued set-valued primitive functions, is represented faithfully
on EXACTLY the same vertices by its singleton split with all output
parts (F,q).

The kernel-checked equivalence of function-closed sets for B and
B.splitOutputParts immediately implies equality of the ENTIRE
closure operators on every literal seed set S. It also preserves
the predicate GeneratedBy S and the minimal finite generator
budget without modifying or closing the seed Finset.

This is the precise rank bookkeeping required when replaying the
corrected 2019 U-closed weak-substructure induction in the native
functional language. It does not turn a weak test into a closed
test at no cardinal cost, or prove compatible strict TARGET
B-tree completions across arbitrary nonclosed HJ histories.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The entire native MULTIVALUED function-generated hull
agrees, on the same exact vertices, with the hull generated
by ALL canonical per-output-part SINGLETON operations.

No vertex, function value, output part or seed generator is lost. -/
theorem System.functionClosure_splitOutputParts
    (B : System L P V) (S : Set V) :
    B.toStructure.functionClosure S =
      (B.splitOutputParts).toStructure.functionClosure S := by
  ext x
  constructor
  · intro hx T hT hST
    exact hx T
      ((B.isClosed_iff_splitOutputParts_isClosed T).mpr hT) hST
  · intro hx T hT hST
    exact hx T
      ((B.isClosed_iff_splitOutputParts_isClosed T).mp hT) hST

/-- The very SAME source seed set generates the original
multivalued functional structure iff it generates its
per-output-part singletonization. -/
theorem System.generatedBy_iff_splitOutputParts
    (B : System L P V) (S : Set V) :
    B.toStructure.GeneratedBy S ↔
      (B.splitOutputParts).toStructure.GeneratedBy S := by
  change B.toStructure.functionClosure S = Set.univ ↔
    (B.splitOutputParts).toStructure.functionClosure S = Set.univ
  rw [B.functionClosure_splitOutputParts S]

/-- An exact finite generator bound is invariant under
per-output-part singletonization, using the SAME finite
set of generators and its UNCHANGED cardinality.

This is a generator-rank statement, NOT an authorization
to replace an n-vertex weak test by its potentially much
larger closed hull. -/
theorem System.generatedByAtMost_iff_splitOutputParts
    (B : System L P V) (n : ℕ) :
    B.toStructure.GeneratedByAtMost n ↔
      (B.splitOutputParts).toStructure.GeneratedByAtMost n := by
  constructor
  · rintro ⟨S, hS, hGen⟩
    exact ⟨S, hS,
      (B.generatedBy_iff_splitOutputParts (↑S : Set V)).mp hGen⟩
  · rintro ⟨S, hS, hGen⟩
    exact ⟨S, hS,
      (B.generatedBy_iff_splitOutputParts (↑S : Set V)).mpr hGen⟩

end StructuralRamsey.FunctionalPartite

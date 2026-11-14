import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Structure.PartialSetFunctionsClosed
import PartiteConstruction.Structure.PartialSetFunctionsTransversal

/-!
# Appendix Track B: original 2019 partial projection need NOT preserve closure equality

The faithful original-2019 partial homomorphism requires preservation
of every DEFINED source value (including defined-empty) but DOES NOT
require an undefined source input to remain undefined at the target.

A two-vertex unary example with identity map is enough: the source
operation is undefined everywhere; the target operation has value {1}
everywhere. The identity map is injective and original source-defined
partial, but closure of {0} in the source is just {0}, while closure
of {0} in the target contains 1. Thus even an injective original
partial homomorphism need not transport generated-closure images
by EQUALITY. The correct universal theorem is the proved one-way
inclusion; full source/target domain reflection is substantive.

Both partial structures are output-transversal for the identity
part map (the target output fibre is a singleton). This example
therefore does not rely on a nontransversal source.
-/

namespace StructuralRamsey.PartialSetStructure.TrackBOriginalPartialStrictClosure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

def src : PartialSetStructure exampleLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := none

def dst : PartialSetStructure exampleLanguage (Fin 2) where
  rel R := Empty.elim R
  func _ _ := some ({1} : Set (Fin 2))

def seed : Set (Fin 2) := {0}

/-- The injective identity is a genuine original-2019 source-defined
homomorphism: all source applications are undefined, so there is NO
false requirement to reflect the target-defined application. -/
theorem original_partial_identity :
    IsOriginalPartialHomomorphism src dst (id : Fin 2 → Fin 2) := by
  constructor
  · intro R x
    exact Empty.elim R
  · intro F x U h
    simp [src] at h

/-- The source has no defined function values, so ANY subset is closed. -/
theorem source_all_closed (S : Set (Fin 2)) : src.IsClosed S := by
  intro F xs U _ h
  simp [src] at h

/-- The source generated closure of {0} does not contain 1. -/
theorem source_closure_excludes_one :
    (1 : Fin 2) ∉ src.functionClosure seed := by
  rw [src.functionClosure_eq_of_isClosed (source_all_closed seed)]
  simp [seed]

/-- Every target closed set containing 0 also contains 1, since
the original target unary F(0) is the singleton {1}. -/
theorem target_closure_contains_one :
    (1 : Fin 2) ∈ dst.functionClosure seed := by
  apply (dst.mem_functionClosure_iff seed 1).mpr
  intro S hClosed hSeed
  have hZero : (0 : Fin 2) ∈ S := hSeed (by simp [seed])
  exact hClosed () (fun _ : Fin 1 => (0 : Fin 2))
    ({1} : Set (Fin 2)) (fun _ => hZero) rfl (by simp)

/-- Injective original-partial map + exact SAME carrier is not enough
for equality of closure images. No weak-subset or power artifact is
involved: even the full two-vertex test and a singleton seed fail. -/
theorem original_partial_not_closure_equal :
    src.functionClosure seed ≠ dst.functionClosure seed := by
  intro h
  have hOne := target_closure_contains_one
  rw [← h] at hOne
  exact source_closure_excludes_one hOne

/-- Both sources are output transversal for identity vertex parts:
the target has singleton nonempty value sets and the source none. -/
theorem target_transversal_identity :
    FibreTransversal dst (id : Fin 2 → Fin 2) := by
  intro F xs U hValue y hy z hz hPart
  exact hPart

theorem source_transversal_identity :
    FibreTransversal src (id : Fin 2 → Fin 2) := by
  intro F xs U hValue y hy z hz hPart
  exact hPart

end StructuralRamsey.PartialSetStructure.TrackBOriginalPartialStrictClosure

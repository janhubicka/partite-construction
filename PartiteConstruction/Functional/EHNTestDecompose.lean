import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Finite closed-test dichotomy for EHN projections

On an irreducible closed test, an EHN projection is literally represented by
a full embedding into the outer structure.  Therefore every finite closed test
has a sharp dichotomy:

* either its projected map is a full embedding; or
* the test admits a proper free decomposition.

This is the strong-induction split used by functional local sparsening.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P W : Type v}
variable {D : Structure L P}
variable {C : Structure L W}
variable {p : W → P}

/-- A closed finite test either projects by a genuine full embedding or is a
proper free amalgam. -/
theorem IsEHNHomomorphismEmbedding.closedTest_embedding_or_decompose
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W)) :
    let Small := C.induce (↑S : Set W) hS
    let inc : Embedding Small C :=
      inclusion C (↑S : Set W) hS
    (∃ g : Embedding Small D, ∀ x, g x = p (inc x)) ∨
      Nonempty (ProperFreeDecomposition Small) := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  by_cases hIrr : Small.Irreducible
  · left
    exact hp.2 Small hIrr inc
  · right
    by_contra hnone
    exact hIrr
      ((irreducible_iff_noProperFreeDecomposition Small).mpr hnone)

end StructuralRamsey.Structure

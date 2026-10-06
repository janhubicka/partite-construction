import PartiteConstruction.Functional.EHNTestDecompose
import PartiteConstruction.Functional.WeakOperations

/-! # Dichotomy for closed EHN attachment roots

In one EHN Picture step the attachment support is the closed set of vertices
whose outer D-part lies in a fixed copy alpha(A).  The induced support is the
weak restriction of the previous stage, and it carries the canonical EHN
projection to A.

Consequently every finite closed overlap occurring in a mixed attachment has
a sharp dichotomy: either its A-label map is represented by a genuine full
embedding into A, or the overlap itself admits a proper free decomposition.
This is the final recursive split needed to reduce the mixed-root case to an
irreducible labelled root.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P U V : Type v}
variable {D : Structure L P}
variable {A : Structure L U}
variable {B : System L P V}

/-- Closed overlaps in the canonical EHN support either embed into A with the
prescribed labels or properly decompose. -/
theorem closedRoot_embedding_or_decompose
    (hB : B.WeaklyPartiteOver D)
    (alpha : Structure.Embedding A D)
    (RootTest : Finset (B.support alpha.toFunctionEmbedding))
    (hRoot :
      (B.weakRestrict D hB.1 A alpha).toStructure.IsClosed
        (↑RootTest : Set _)) :
    let R :=
      (B.weakRestrict D hB.1 A alpha).toStructure.induce
        (↑RootTest : Set _) hRoot
    let inc : Structure.Embedding R
        (B.weakRestrict D hB.1 A alpha).toStructure :=
      Structure.inclusion _ (↑RootTest : Set _) hRoot
    (∃ g : Structure.Embedding R A,
        ∀ x, g x =
          (B.weakRestrict D hB.1 A alpha).part (inc x)) ∨
      Nonempty (ProperFreeDecomposition R) := by
  exact
    (B.weakRestrict_invariant D hB.1 A alpha hB).
      closedTest_embedding_or_decompose RootTest hRoot

end StructuralRamsey.FunctionalPartite

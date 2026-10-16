import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.EHNFibreBijective

/-!
# Strict full-functional B-trees labelled by an EHN control projection

The genuine functional Hales-Jewett iteration starts from a closed Ramsey
control D. Its partite stages carry an EHN map to D, and EVERY set-valued
function image is transversal with respect to that map.

A strict B-tree completion may also carry a compatible EHN projection to
D. If two labelled strict FULL-FUNCTIONAL B-trees glue along a full
common root contained in an irreducible constituent on each side, and
their control projections agree on the root, then the glued target:
  * remains a strict genuine B-tree;
  * carries a single EHN projection to D;
  * restricts to the prescribed side projections;
  * has TRANSVERSAL images for every genuinely set-valued function.

No root of the source weak TEST is made closed or enlarged here.
The target root used in strict B-tree gluing IS a full embedded
functional structure. This theorem is a reusable engine for making
strict target completions part-labelled, but it does not assert
that compatible rooted completions exist for arbitrary maximal
mixed Hales-Jewett tests.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C VB P : Type v}

/-- Labelled strict B-tree amalgamation in the natural set-valued
function language. An EHN projection automatically makes every
individual operation-output fibre transversal in its projected parts.

The source side/root projections are genuine EHN homomorphism-embeddings,
not later-survey total-fibre homomorphisms reflecting undefined inputs. -/
theorem labelledStrictTree_glue
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB) (D : Structure L P)
    (hTreeL : TreeAmalgam Base E Left)
    (hTreeR : TreeAmalgam Base F Right)
    (hcL : sL.ContainedInIrreducible)
    (hcR : sR.ContainedInIrreducible)
    (pL : E → P) (pR : F → P)
    (hL : Left.IsEHNHomomorphismEmbedding D pL)
    (hR : Right.IsEHNHomomorphismEmbedding D pR)
    (hAgree : ∀ d, pL (sL d) = pR (sR d)) :
    ∃ p : C → P,
      TreeAmalgam Base C Whole ∧
      Whole.IsEHNHomomorphismEmbedding D p ∧
      (∀ x, p (iL x) = pL x) ∧
      (∀ y, p (iR y) = pR y) ∧
      (∀ F (x : Fin (L.funcArity F) → C),
        Set.InjOn p (Whole.func F x)) := by
  obtain ⟨p, hp, hpL, hpR⟩ :=
    hFree.exists_EHN_projection pL pR hL hR hAgree
  have hTree : TreeAmalgam Base C Whole :=
    TreeAmalgam.glue hTreeL hTreeR sL sR hcL hcR iL iR hFree
  refine ⟨p, hTree, hp, hpL, hpR, ?_⟩
  intro F x y hy z hz heq
  exact (hp.injOn_func_of_nonempty F x ⟨y, hy⟩) hy hz heq

end StructuralRamsey.Structure.IsFreeAmalgam

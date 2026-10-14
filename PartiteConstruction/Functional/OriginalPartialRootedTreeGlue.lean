import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Strict full-functional B-tree gluing under ORIGINAL partial maps

The published mixed partite argument needs to glue two B-tree completions
of proper pieces. Their common source root can be reducible; merely having
two independent partial homomorphism-embeddings into B-trees does not allow
gluing, since the restrictions to the root may not be embeddings.

Here we prove the exact sufficient *rooted* version. Suppose each side
has an EHN (original-partial) homomorphism-embedding into a genuine
strict full-functional B-tree, whose root restriction is a specified full
embedding into a constituent irreducible piece. Then free-amalgamate the
TWO TARGET TREES over the common full root and combine the source maps.
This gives an original-partial HE into a strict tree, without requiring
root isolation of the source side maps. Cross-side map collisions are
permitted in the original 2019 partial-HE convention; the source
irreducibles localise to one side of its free amalgam.

This theorem is a conditional compatibility lemma, NOT the existence
of compatible rooted completions for arbitrary mixed native tests.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB VL VR : Type v}

/-- Rooted strict B-tree amalgamation for EHN/original-partial maps.

The source common root may be reducible. What is needed is a FULL root
embedding into each side B-tree, contained in an irreducible B-piece,
and agreement of the side maps with those prescribed embeddings.
No root isolation or global injection of the source maps is assumed. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_glue_rooted
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSource : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (TL : Structure L VL) (TR : Structure L VR)
    (hTL : TreeAmalgam Base VL TL)
    (hTR : TreeAmalgam Base VR TR)
    (rootL : Embedding Root TL) (rootR : Embedding Root TR)
    (hRootL : rootL.ContainedInIrreducible)
    (hRootR : rootR.ContainedInIrreducible)
    (pL : E → VL) (pR : F → VR)
    (hpL : Left.IsEHNHomomorphismEmbedding TL pL)
    (hpR : Right.IsEHNHomomorphismEmbedding TR pR)
    (hLiftL : ∀ x : H, pL (sL x) = rootL x)
    (hLiftR : ∀ x : H, pR (sR x) = rootR x) :
    HasOriginalPartialTreeCompletion Base Whole := by
  let Target := FreeAmalgam.amalgam Root TL TR rootL rootR
  let jL := FreeAmalgam.leftEmbedding Root TL TR rootL rootR
  let jR := FreeAmalgam.rightEmbedding Root TL TR rootL rootR
  have hTarget : IsFreeAmalgam rootL rootR jL jR :=
    FreeAmalgam.isFreeAmalgam Root TL TR rootL rootR
  have hTree : TreeAmalgam Base _ Target :=
    TreeAmalgam.glue hTL hTR rootL rootR hRootL hRootR
      jL jR hTarget
  have hMapL : Left.IsEHNHomomorphismEmbedding Target (jL ∘ pL) :=
    jL.isEHNHomomorphismEmbedding.comp hpL
  have hMapR : Right.IsEHNHomomorphismEmbedding Target (jR ∘ pR) :=
    jR.isEHNHomomorphismEmbedding.comp hpR
  have hMatch : ∀ x : H,
      (jL ∘ pL) (sL x) = (jR ∘ pR) (sR x) := by
    intro x
    change jL (pL (sL x)) = jR (pR (sR x))
    rw [hLiftL x, hLiftR x]
    exact (hTarget.overlap (rootL x) (rootR x)).mpr
      ⟨x, rfl, rfl⟩
  obtain ⟨p, hp, _hL, _hR⟩ :=
    hSource.exists_EHN_projection
      (jL ∘ pL) (jR ∘ pR) hMapL hMapR hMatch
  exact ⟨_, Target, hTree, p, hp.toOriginalPartial⟩

end StructuralRamsey.Structure

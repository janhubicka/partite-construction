import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue

/-!
# Rooted strict B-tree witnesses with a FULL source-side embedding

The 2019 original-partial functional mixed induction needs a strict
relative B-tree extension over a fixed completion of the actual closed
separator. General EHN side completions may collapse reducible roots.

There is a complementary positive case independent of root
irreducibility: whenever a side has a FULL embedding into an existing
strict B-tree, and the embedded common root lies in an irreducible
constituent piece of that tree, we can freely glue this whole tree
to a freshly prescribed Base copy along the same root.

This is a strict TreeExtension FROM Base; its side completion map is
itself FULL, not merely original-partial, and extends the prescribed
root embedding into Base exactly. Nothing about the root's
irreducibility or its generator rank is required. The target root is
a full embedding into Base, so noninjective root quotient maps are
not asserted to be covered.

In the especially useful one-copy case Side embeds into Base itself,
root containment is automatic because Base is irreducible. The
source side may be a REDUCIBLE full substructure of Base.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E VB X : Type v}

/-- A full embedding of Side into a STRICT B-tree can be rerooted over
ANY prescribed full common-root embedding into Base, provided that
the root image of the side lies in one irreducible constituent
substructure of its target tree.

The original strict B-tree is attached to Start=Base along the
displayed full root embeddings; the right-side embedding provides
a FULL rooted completion of Side. This does not require the source
root to be irreducible or one-generated. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_full_tree_rooted
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (T : Structure L X)
    (hT : TreeAmalgam Base X T)
    (eSide : Embedding Side T)
    (hRootT : (eSide.comp s).ContainedInIrreducible) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  let tRoot : Embedding Root T := eSide.comp s
  let Target := FreeAmalgam.amalgam Root Base T q tRoot
  have hQ : q.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro x
    exact ⟨q x, rfl⟩
  let ext : TreeExtension Base Base _ Target :=
    TreeExtension.attachTree TreeExtension.refl
      hT q tRoot hQ hRootT
  let j : Embedding T Target :=
    FreeAmalgam.rightEmbedding Root Base T q tRoot
  let pSide : Embedding Side Target := j.comp eSide
  have hFree : IsFreeAmalgam q tRoot
      (FreeAmalgam.leftEmbedding Root Base T q tRoot) j :=
    FreeAmalgam.isFreeAmalgam Root Base T q tRoot
  refine ⟨_, Target, ext, pSide,
    pSide.isEHNHomomorphismEmbedding.toOriginalPartial, ?_⟩
  intro x
  change j (eSide (s x)) =
    (FreeAmalgam.leftEmbedding Root Base T q tRoot) (q x)
  exact ((hFree.overlap (q x) (tRoot x)).mpr
    ⟨x, rfl, rfl⟩).symm

/-- In particular, if the entire side embeds FULLY into Base, then
it admits a STRICT relative B-tree completion over any prescribed
FULL root embedding into Base. The common root can be reducible,
can contain many vertices, and needs no generator bound.

A suitable rooted two-copy free amalgam is constructed directly;
it is not required that the side embedding into Base agree with
the prescribed root embedding before this construction. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_full_side_in_base
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (eSide : Embedding Side Base) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  have hRoot : (eSide.comp s).ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro x
    exact ⟨eSide (s x), rfl⟩
  exact HasOriginalPartialTreeExtensionCompletion.of_full_tree_rooted
    Base hBase s q Base hTree eSide hRoot

end StructuralRamsey.Structure

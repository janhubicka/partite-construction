import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Synchronizing strict original-partial completions over an IRREDUCIBLE root

The general maximal-mixed case of Appendix A needs two strict B-tree
completions extending one and the same strict tree completion of its
actual (possibly reducible) common separator.

For an IRREDUCIBLE common separator, the compatibility follows from
the *absolute* original-2019 partial homomorphism-embedding completion
of each side. Its restriction to the irreducible separator is a FULL
embedding; the root image sits in an irreducible constituent B-copy
of the target tree. Attach a fresh prescribed Base copy to the side
tree along the full embedded root. Read the result as a strict
TreeExtension of that same prescribed Base. This is the exact
relative witness, with no assumption that the two independently
chosen side witnesses already carry compatible labels.

Applying this independently to both sides, the already verified
original-partial common-root gluing theorem merges them.

The genuinely missing geometric input in the published maximal
mixed-attachment induction is therefore concentrated in:
 - reducible actual common separators; or
 - obtaining absolute strict side completions within the available
   generator budget.

This theorem is independent of EHN geometry and useful wherever a
full free amalgam is mapped partially into strict B-trees.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB : Type v}

/-- An ABSOLUTE strict original-partial completion of a side converts
to a strict relative completion over any prescribed full embedding
of an IRREDUCIBLE source root into Base.

The target is obtained by strict full-functional free amalgamation
of the original side B-tree with a fresh Base-copy along the embedded
source root. It is a TreeExtension of the prescribed Base, not merely
an unrelated tree admitting the separator somewhere inside. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hRoot : Root.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (hSide : HasOriginalPartialTreeCompletion Base Side) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  classical
  obtain ⟨Z, T, hTree, p, hp⟩ := hSide
  obtain ⟨toT, hToT⟩ := hp.toEHN.2 Root hRoot s
  have hcT : toT.ContainedInIrreducible := by
    obtain ⟨j, hj⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy
        hRoot toT
    exact ⟨VB, Base, hBase, j, hj⟩
  have hcBase : q.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro x
    exact ⟨q x, rfl⟩
  let NewTarget := FreeAmalgam.amalgam Root Base T q toT
  let ext : TreeExtension Base Base _ NewTarget :=
    TreeExtension.attachTree TreeExtension.refl
      hTree q toT hcBase hcT
  let jT : Embedding T NewTarget :=
    FreeAmalgam.rightEmbedding Root Base T q toT
  let pNew : E → FreeAmalgam.Vertex Root Base T q toT :=
    jT ∘ p
  have hpNew : IsOriginalPartialHomomorphismEmbedding
      Side NewTarget pNew :=
    jT.isEHNHomomorphismEmbedding.toOriginalPartial.comp hp
  refine ⟨_, NewTarget, ext, pNew, hpNew, ?_⟩
  intro x
  have hFree : IsFreeAmalgam q toT
      (FreeAmalgam.leftEmbedding Root Base T q toT) jT :=
    FreeAmalgam.isFreeAmalgam Root Base T q toT
  change jT (p (s x)) =
    (FreeAmalgam.leftEmbedding Root Base T q toT) (q x)
  rw [← hToT x]
  exact ((hFree.overlap (q x) (toT x)).mpr
    ⟨x, rfl, rfl⟩).symm

/-- If the FULL source root of a free amalgam is irreducible and has
a prescribed full embedding into Base, any two absolute strict
original-partial B-tree completions of its sides can be synchronized
over that ONE Base copy, and hence glued to an absolute strict
completion of the whole free amalgam.

No root-isolation assumption or arbitrary choice of compatible side
representatives is required at this level. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_of_irreducible_root
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hRoot : Root.Irreducible)
    (q : Embedding Root Base)
    (hLeft : HasOriginalPartialTreeCompletion Base Left)
    (hRight : HasOriginalPartialTreeCompletion Base Right) :
    HasOriginalPartialTreeCompletion Base Whole := by
  have hRelL :
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sL q :=
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sL q hLeft
  have hRelR :
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sR q :=
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sR q hRight
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x,rfl⟩)
  exact hSrc.originalPartialTreeCompletion_glue_relative
    Base hTree q hRelL hRelR

end StructuralRamsey.Structure

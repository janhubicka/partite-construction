import PartiteConstruction.Functional.TreeExtension
import PartiteConstruction.Functional.WitnessGlue

/-! # Gluing side witnesses over a common strict root tree

The ordinary functional witness glue requires the target root to lie inside
one irreducible constituent copy.  That is too strong for a reducible closed
overlap.

If both side witnesses are instead obtained as strict extensions of the same
root tree, `TreeExtension.mergeFree_tree` embeds their free amalgam over that
whole root tree into a further strict tree.  The existing exact functional
lift then completes the source free amalgam without any irreducibility
assumption on the root tree itself.
-/

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {VB H E F C G ZL ZR : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {Start : Structure L G}
variable {TL : Structure L ZL} {TR : Structure L ZR}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Glue two functional side witnesses which extend one common strict
root-tree.  The source overlap may be reducible. -/
theorem glueTreeExtensions
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hStart : TreeAmalgam Base G Start)
    (hExtL : TreeExtension Base Start ZL TL)
    (hExtR : TreeExtension Base Start ZR TR)
    (q : H → G)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = hExtL.startEmbedding (q d))
    (hcompatR : ∀ d, fR (sR d) = hExtR.startEmbedding (q d))
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hrootL :
      IsFreeAmalgam.RootIsolated
        sL hExtL.startEmbedding q fL)
    (hrootR :
      IsFreeAmalgam.RootIsolated
        sR hExtR.startEmbedding q fR) :
    HasTreeCompletion Base Whole := by
  obtain ⟨Z, Target, hTree, eL, eR, hTgt⟩ :=
    hExtL.mergeFree_tree hStart hExtR
  let f : C → Z :=
    IsFreeAmalgam.functionalLiftMap
      hSrc hTgt q fL fR hcompatL hcompatR
  have hf : Whole.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  exact ⟨Z, Target, hTree, f, hf⟩

end StructuralRamsey.Structure.LocallyClosedTreeCompletable

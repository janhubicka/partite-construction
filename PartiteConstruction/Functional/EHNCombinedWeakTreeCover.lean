import PartiteConstruction.Functional.EHNWeakAttachmentStep
import PartiteConstruction.Functional.EHNProjectedCover

/-!
# One native functional attachment preserves BOTH iteration invariants

The corrected published iterated proof needs local graph-tree control and
the projected irreducible-into-B property on the SAME genuine functional
Picture. Both properties already have separate verified native binary
attachment lemmas. Here they are carried simultaneously through exactly
the same attachment, with no repeat of the recursive Ramsey argument and
no U-closed relational stages.

This is a local ingredient for eventually performing the final B-copy
attachment of the published sparsening proof while retaining the weak
vertex-size bound. The full combined EHN Picture/n-pass theorem and the
strict full-functional mixed-root completion are not asserted here.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U VB P : Type v}
variable {K : Structure.StructureClass (L := L)}

/-- One actual full native free attachment preserves BOTH the
projected B-copy cover and the n-vertex graph-tree history invariant. -/
theorem Stage.attach_weakTree_and_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L VB)
    (D : Structure L P)
    [Finite U] [Finite VB] [Finite P]
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (Old T : Stage K D)
    (S : Set Old.Carrier)
    (hS : Old.system.toStructure.IsClosed S)
    (f : FunctionalPartite.Embedding (Old.system.induce S hS) T.system)
    (α : Structure.Embedding A D)
    (hSupport : ∀ x : Old.Carrier, x ∈ S →
      ∃ a : U, Old.system.part x = α a)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike
      A.graph Base.graph D.graph (n - 1))
    (hOldTree : RelStructure.LocallyTreeLike
      A.graph Base.graph Old.system.toStructure.graph n)
    (hCoreTree : RelStructure.LocallyTreeLike
      A.graph Base.graph T.system.toStructure.graph n)
    (hOldCover : Old.ProjectedCover Base)
    (hCoreCover : T.ProjectedCover Base) :
    let R := T.attach hK Old.system Old.isPartite Old.mem S hS f
    RelStructure.LocallyTreeLike A.graph Base.graph
      R.system.toStructure.graph n ∧
    R.ProjectedCover Base := by
  constructor
  · exact Stage.attach_weakGraphLocallyTreeLike
      hK A Base D hA eAB Old T S hS f α hSupport
      n hn hD hOldTree hCoreTree
  · exact T.attach_projectedCover
      hK Base Old.system Old.isPartite Old.mem S hS f
      hCoreCover hOldCover

end StructuralRamsey.FunctionalPartite.EHN

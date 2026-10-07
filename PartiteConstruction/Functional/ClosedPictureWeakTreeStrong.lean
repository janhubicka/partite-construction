import PartiteConstruction.Functional.ClosedPictureWeakTree
import PartiteConstruction.Iterated.WeakStep

/-! # Strong weak-substructure tree invariant in a closed functional Picture

The extra control of ambient A-copies in the relational local-tree invariant
is what makes the vertex-size bound iterable. The actual U-closed functional
Picture is an induced substructure of the ordinary relational Picture,
because it attaches only the subfamily of U-closed support embeddings.
Thus the already validated strong one-step relational theorem transfers
without any change to the test carrier.

The hereditary irreducibility assumption is explicit: the controlled
relational theorem needs it, even though the weaker completion-only
theorem does not.
-/

namespace StructuralRamsey.Partite.Closed.Picture

open RelStructure

universe u v
variable {L : Language.{u}} {P U V W VB : Type v}

/-- The actual closed functional Picture step preserves full controlled
local tree-likeness of all weak vertex substructures at size n, assuming
the fixed control D has the invariant at the preceding size n-1. -/
theorem locallyTreeLike_weakStep
    (A : RelStructure L.graph U)
    (Base : RelStructure L.graph VB)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    [Finite U] [Finite VB] [Finite P] [Finite V]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A Base D (n - 1))
    (hOld : RelStructure.LocallyTreeLike A Base B.toRelStructure n)
    (hPartite : B.IsPartiteOver D)
    (N : ℕ) (hN : 0 < N) :
    let E := Partite.Induced.power
      (B.restrict α.toEmbedding.toFunctionEmbedding) N
    RelStructure.LocallyTreeLike A Base
      (build A D B α E).toRelStructure n := by
  let E := Partite.Induced.power
    (B.restrict α.toEmbedding.toFunctionEmbedding) N
  have hOrd :
      RelStructure.LocallyTreeLike A Base
        (Partite.Picture.build
          B α.toEmbedding.toFunctionEmbedding E).toRelStructure n :=
    Partite.Iterated.canonicalStep_locallyTreeLike
      A Base D B α.toEmbedding hA eAB n hn hD hOld hPartite N hN
  exact hOrd.pullback_embedding (toOrdinaryRelEmbedding A D B α E)

end StructuralRamsey.Partite.Closed.Picture

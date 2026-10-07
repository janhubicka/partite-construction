import PartiteConstruction.Functional.EHNProjectionGraphBridge
import PartiteConstruction.Partite.Induced

/-! # Graph partite-system view of a genuine functional EHN stage

The native functional iteration requires no U-closed relational embeddings:
every stage is a genuine set-valued-function system and all attachments are
over actual function-closed supports.

For the vertex-size induction one may *inspect* a native system via the
graph of its functions.  Its EHN weak projection is already a relational
homomorphism-embedding on irreducible weak tests.  Consequently the graph
is an ordinary relational partite system, without strengthening the native
projection to a fibre-surjective function homomorphism.

This bridge does not change the carrier, function interpretations or the
native Hales--Jewett/Picture construction.  It is only a way to reuse
the relational weak-substructure tree-completion lemmas.
-/

namespace StructuralRamsey.FunctionalPartite.System

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- A genuine functional system with an EHN weak projection has a
relational partite-system view on its function graph.  In a graph tuple,
the vertices form an irreducible weak test, so their parts are distinct
unless they are literally the same vertex. -/
def toGraphPartite
    (B : FunctionalPartite.System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) :
    Partite.System L.graph P V where
  toRelStructure := B.toStructure.graph
  part := B.part
  transversal := by
    intro R z hz i j hij
    let S : Set V := Set.range z
    have hS : (B.toStructure.graph.induce S).Irreducible := by
      intro x y _
      obtain ⟨ix, hix⟩ := x.2
      obtain ⟨iy, hiy⟩ := y.2
      let zz : Fin (L.graph.arity R) → S :=
        fun k => ⟨z k, ⟨k, rfl⟩⟩
      refine ⟨R, zz, ix, iy, ?_, ?_, ?_⟩
      · change B.toStructure.graph.rel R (Subtype.val ∘ zz)
        have heq : (Subtype.val ∘ zz) = z := by
          funext k
          rfl
        rw [heq]
        exact hz
      · apply Subtype.ext
        exact hix
      · apply Subtype.ext
        exact hiy
    have hp : B.toStructure.graph.IsHomomorphismEmbedding D.graph B.part :=
      hB.graphHomomorphismEmbedding
    exact hp.injOn S hS ⟨i, rfl⟩ ⟨j, rfl⟩ hij

/-- The graph view of an EHN functional system projects
homomorphism-embeddingly into the control graph, exactly as required by
the relational weak-substructure induction. -/
theorem toGraphPartite_isPartiteOver
    (B : FunctionalPartite.System L P V)
    (D : Structure L P) (hB : B.WeaklyPartiteOver D) :
    (B.toGraphPartite D hB).IsPartiteOver D.graph := by
  exact hB.graphHomomorphismEmbedding

end StructuralRamsey.FunctionalPartite.System

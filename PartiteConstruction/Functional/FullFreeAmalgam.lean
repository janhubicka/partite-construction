import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Iterated.FreeAmalgam

/-! # Concrete free amalgams in languages with functions

We construct a genuine free amalgam of full relation/function structures by
forming the relational free amalgam of their graph encodings.  Since the two
root maps come from full embeddings, they are function-closed.  Hence the
canonical side embeddings are function-closed as well and decode to full
embeddings.

This module deliberately keeps irreducibility in the *full* function-language
sense.  No implication from functional irreducibility to irreducibility of the
relational graph encoding is used.
-/

namespace StructuralRamsey.Structure.FreeAmalgam

universe u v

variable {L : Language.{u}}
variable {U V W Q : Type v}

variable (D : Structure L U) (A : Structure L V) (B : Structure L W)
variable (fA : Embedding D A) (fB : Embedding D B)

abbrev Vertex :=
  RelStructure.FreeAmalgam.Vertex D.graph A.graph B.graph fA.graph fB.graph

noncomputable def relAmalgam :
    RelStructure L.graph (Vertex D A B fA fB) :=
  RelStructure.FreeAmalgam.amalgam
    D.graph A.graph B.graph fA.graph fB.graph

noncomputable def amalgam :
    Structure L (Vertex D A B fA fB) :=
  Structure.ofGraph (relAmalgam D A B fA fB)

private theorem rel_sides_closed :
    let hfree :=
      RelStructure.FreeAmalgam.isFreeAmalgam
        D.graph A.graph B.graph fA.graph fB.graph
    RelStructure.FunctionClosedMap A.graph (relAmalgam D A B fA fB)
        (RelStructure.FreeAmalgam.leftEmbedding
          D.graph A.graph B.graph fA.graph fB.graph) ∧
      RelStructure.FunctionClosedMap B.graph (relAmalgam D A B fA fB)
        (RelStructure.FreeAmalgam.rightEmbedding
          D.graph A.graph B.graph fA.graph fB.graph) := by
  dsimp
  exact
    (RelStructure.FreeAmalgam.isFreeAmalgam
      D.graph A.graph B.graph fA.graph fB.graph).sides_closed_iff.mpr
      ⟨fA.toClosedGraph.closed, fB.toClosedGraph.closed⟩

noncomputable def leftEmbedding :
    Embedding A (amalgam D A B fA fB) :=
  Structure.Embedding.ofClosedGraphTarget {
    toEmbedding :=
      RelStructure.FreeAmalgam.leftEmbedding
        D.graph A.graph B.graph fA.graph fB.graph
    closed := (rel_sides_closed D A B fA fB).1
  }

noncomputable def rightEmbedding :
    Embedding B (amalgam D A B fA fB) :=
  Structure.Embedding.ofClosedGraphTarget {
    toEmbedding :=
      RelStructure.FreeAmalgam.rightEmbedding
        D.graph A.graph B.graph fA.graph fB.graph
    closed := (rel_sides_closed D A B fA fB).2
  }

/-- The concrete graph construction is a genuine full free amalgam. -/
theorem isFreeAmalgam :
    IsFreeAmalgam fA fB
      (leftEmbedding D A B fA fB) (rightEmbedding D A B fA fB) := by
  classical
  let hrel :=
    RelStructure.FreeAmalgam.isFreeAmalgam
      D.graph A.graph B.graph fA.graph fB.graph
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    rcases hrel.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨b, hb⟩
  · intro a b
    change
      (RelStructure.FreeAmalgam.leftEmbedding
          D.graph A.graph B.graph fA.graph fB.graph) a =
        (RelStructure.FreeAmalgam.rightEmbedding
          D.graph A.graph B.graph fA.graph fB.graph) b ↔ _
    exact hrel.overlap a b
  · intro R z
    change
      (relAmalgam D A B fA fB).rel (.inl R) z ↔
        (∃ x : Fin (L.relArity R) → V,
          A.rel R x ∧
            z = (RelStructure.FreeAmalgam.leftEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) ∘ x) ∨
        (∃ y : Fin (L.relArity R) → W,
          B.rel R y ∧
            z = (RelStructure.FreeAmalgam.rightEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) ∘ y)
    exact hrel.rel_iff (.inl R) z
  · intro F x y
    change
      (relAmalgam D A B fA fB).rel (.inr F)
          (Structure.funcTuple x y) ↔
        (∃ a : Fin (L.funcArity F) → V, ∃ b : V,
          b ∈ A.func F a ∧
            x = (RelStructure.FreeAmalgam.leftEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) ∘ a ∧
            y = (RelStructure.FreeAmalgam.leftEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) b) ∨
        (∃ a : Fin (L.funcArity F) → W, ∃ b : W,
          b ∈ B.func F a ∧
            x = (RelStructure.FreeAmalgam.rightEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) ∘ a ∧
            y = (RelStructure.FreeAmalgam.rightEmbedding
              D.graph A.graph B.graph fA.graph fB.graph) b)
    constructor
    · intro h
      rcases (hrel.rel_iff (.inr F)
          (Structure.funcTuple x y)).mp h with
        ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
      · let a : Fin (L.funcArity F) → V :=
          fun k => q k.castSucc
        let b : V := q (Fin.last (L.funcArity F))
        refine Or.inl ⟨a, b, ?_, ?_, ?_⟩
        · exact (Structure.graph_func_snoc A F a b).mp (by
            simpa [a, b] using hq)
        · funext k
          have hk := congrFun heq k.castSucc
          simpa [a, Structure.funcTuple] using hk
        · have hk := congrFun heq (Fin.last (L.funcArity F))
          simpa [b, Structure.funcTuple] using hk
      · let a : Fin (L.funcArity F) → W :=
          fun k => q k.castSucc
        let b : W := q (Fin.last (L.funcArity F))
        refine Or.inr ⟨a, b, ?_, ?_, ?_⟩
        · exact (Structure.graph_func_snoc B F a b).mp (by
            simpa [a, b] using hq)
        · funext k
          have hk := congrFun heq k.castSucc
          simpa [a, Structure.funcTuple] using hk
        · have hk := congrFun heq (Fin.last (L.funcArity F))
          simpa [b, Structure.funcTuple] using hk
    · rintro (⟨a, b, hb, hx, hy⟩ | ⟨a, b, hb, hx, hy⟩)
      · apply (hrel.rel_iff (.inr F)
          (Structure.funcTuple x y)).mpr
        refine Or.inl ⟨Structure.funcTuple a b,
          (Structure.graph_func_snoc A F a b).2 hb, ?_⟩
        rw [hx, hy]
        exact
          (Structure.comp_funcTuple
            (fun z =>
              RelStructure.FreeAmalgam.leftEmbedding
                D.graph A.graph B.graph fA.graph fB.graph z)
            a b).symm
      · apply (hrel.rel_iff (.inr F)
          (Structure.funcTuple x y)).mpr
        refine Or.inr ⟨Structure.funcTuple a b,
          (Structure.graph_func_snoc B F a b).2 hb, ?_⟩
        rw [hx, hy]
        exact
          (Structure.comp_funcTuple
            (fun z =>
              RelStructure.FreeAmalgam.rightEmbedding
                D.graph A.graph B.graph fA.graph fB.graph z)
            a b).symm

/-- Free-amalgaming two genuine functional tree amalgams over a full root
produces another genuine functional tree amalgam whenever the two root images
satisfy the survey's irreducible-containment condition. -/
theorem treeAmalgam
    (Base : Structure L Q)
    (hA : TreeAmalgam Base V A)
    (hB : TreeAmalgam Base W B)
    (hcA : fA.ContainedInIrreducible)
    (hcB : fB.ContainedInIrreducible) :
    TreeAmalgam Base (Vertex D A B fA fB) (amalgam D A B fA fB) :=
  TreeAmalgam.glue hA hB fA fB hcA hcB
    (leftEmbedding D A B fA fB) (rightEmbedding D A B fA fB)
    (isFreeAmalgam D A B fA fB)

end StructuralRamsey.Structure.FreeAmalgam

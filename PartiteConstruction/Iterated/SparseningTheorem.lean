import PartiteConstruction.Iterated.SparseningIteration
import PartiteConstruction.Iterated.FinalSparsening

/-! # A checked strengthened sparsening theorem

This assembles the verified iterated induced construction with the verified
final finite attachment phase.  It proves the relational sparsening theorem
for positive \`n\` under the sufficient hereditary-irreducibility assumptions
identified by the formalization.

The output simultaneously has the Ramsey arrow, a homomorphism-embedding back
to the original Ramsey witness, the strengthened local-tree invariant, and the
property that every irreducible substructure extends to a copy of \`B\`.
-/
namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- End-to-end sparsening under hereditary irreducibility of both the control
structure and the base structure. -/
theorem sparseningRamsey_hereditarilyIrreducible
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hA : A.HereditarilyIrreducible)
    (hB : B.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  obtain ⟨S, _⟩ :=
    build A B C₀ κ hRamsey hA eAB n hn
  letI : Fintype S.Vertex := Fintype.ofFinite S.Vertex
  obtain ⟨T, hExtend⟩ :=
    RelStructure.FinalSparsening.build_all
      A B S.C C₀ n S.projection
      hA eAB hB
      S.projectionHE S.locallyTreeLike S.projected
  have hArrow :
      StructuralRamsey.Arrow A B T.C κ :=
    S.arrow.of_embedding T.core
  exact ⟨T.Vertex, inferInstance, T.C, hArrow,
    T.projection, T.projectionHE, T.locallyTreeLike, hExtend⟩


/-- Strengthened relational sparsening theorem with no separate embedding
assumption and for every size bound \`n\`.

If \`A\` does not embed into \`B\`, the Ramsey arrow inside a copy of \`B\` is
vacuous, so \`B\` itself is already a witness.  Otherwise we run the checked
positive-level construction at level \`n+1\` and then use monotonicity of local
tree-likeness. -/
theorem sparseningRamsey_hereditarilyIrreducible_all
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hA : A.HereditarilyIrreducible)
    (hB : B.HereditarilyIrreducible)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  by_cases hAB : Nonempty (RelStructure.Embedding A B)
  · let eAB : RelStructure.Embedding A B := Classical.choice hAB
    obtain ⟨Z, hZ, C, hArrow, p, hp, hLocal, hExt⟩ :=
      sparseningRamsey_hereditarilyIrreducible
        A B C₀ κ hRamsey hA hB eAB (n + 1) (by omega)
    refine ⟨Z, hZ, C, hArrow, p, hp, ?_, hExt⟩
    exact hLocal.mono (Nat.le_succ n)
  · letI : IsEmpty (RelStructure.Embedding A B) :=
      ⟨fun e => hAB ⟨e⟩⟩
    letI : Nonempty (RelStructure.Embedding B C₀) :=
      Partite.Induced.nonempty_embedding_of_arrow A B C₀ κ hRamsey
    let β : RelStructure.Embedding B C₀ :=
      Classical.choice (inferInstance : Nonempty (RelStructure.Embedding B C₀))
    have hArrowSelf : StructuralRamsey.Arrow A B B κ :=
      StructuralRamsey.arrow_of_isEmpty
    have hLocal : RelStructure.LocallyTreeLike A B B n :=
      RelStructure.LocallyTreeLike.base A B n
    have hExt : RelStructure.IrreduciblesExtendTo B B := by
      intro S _
      refine ⟨RelStructure.Embedding.id B, ?_⟩
      intro z
      exact ⟨z.1, rfl⟩
    exact ⟨VB, inferInstance, B, hArrowSelf,
      β, β.isHomomorphismEmbedding, hLocal, hExt⟩

end StructuralRamsey.Partite.IteratedSparsening

import PartiteConstruction.Iterated.SparseningIteration
import PartiteConstruction.Iterated.FinalSupportIteration

/-! # Sparsening with uniform final completion

This replaces the old sequential final attachment, which required hereditary
irreducibility of the base, by support-grouped simultaneous attachments.

The iterated induced construction still uses hereditary irreducibility of the
control structure in its mixed step.  The final phase, however, now requires
only irreducibility of the control and no hereditary assumption on the base.
-/
namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- End-to-end relational sparsening with hereditary irreducibility required
only for the control structure.  The final support-grouped completion places
no hereditary irreducibility assumption on B. -/
theorem sparseningRamsey_uniformFinal
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  letI : Fintype UA := Fintype.ofFinite UA
  letI : Fintype VB := Fintype.ofFinite VB
  let M := RelStructure.UniformFinal.finalSupportBudget UA VB n
  obtain ⟨S, _⟩ :=
    build A B C₀ κ hRamsey hA eAB (M + 1) (by omega)
  have hLocalM : RelStructure.LocallyTreeLike A B S.C M :=
    S.locallyTreeLike.mono (Nat.le_succ M)
  letI : Fintype S.Vertex := Fintype.ofFinite S.Vertex
  obtain ⟨T, hExtend⟩ :=
    RelStructure.UniformFinal.build_all_supports
      A B S.C C₀ S.projection
      hA.irreducible S.projectionHE S.projected n hLocalM
  have hArrow : StructuralRamsey.Arrow A B T.C κ :=
    S.arrow.of_embedding T.core
  exact ⟨T.Vertex, inferInstance, T.C, hArrow,
    T.projection, T.projectionHE, T.locallyTreeLike, hExtend⟩

/-- All size bounds and no separate A-to-B hypothesis.  If A does not embed
into B, B itself is the vacuous Ramsey witness. -/
theorem sparseningRamsey_uniformFinal_all
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hA : A.HereditarilyIrreducible)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  by_cases hAB : Nonempty (RelStructure.Embedding A B)
  · exact sparseningRamsey_uniformFinal
      A B C₀ κ hRamsey hA (Classical.choice hAB) n
  · letI : IsEmpty (RelStructure.Embedding A B) :=
      ⟨fun e => hAB ⟨e⟩⟩
    letI : Nonempty (RelStructure.Embedding B C₀) :=
      Partite.Induced.nonempty_embedding_of_arrow A B C₀ κ hRamsey
    let beta : RelStructure.Embedding B C₀ :=
      Classical.choice
        (inferInstance : Nonempty (RelStructure.Embedding B C₀))
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
      beta, beta.isHomomorphismEmbedding, hLocal, hExt⟩

end StructuralRamsey.Partite.IteratedSparsening

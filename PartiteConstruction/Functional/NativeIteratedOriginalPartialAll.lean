import PartiteConstruction.Functional.NativeIteratedOriginalPartial
import PartiteConstruction.Functional.EHNInitialWeakTree

/-!
# Native functional sparsening with no artificial A ↪ B hypothesis

The already verified n-pass functional iterated construction assumes an
embedding A ↪ B to initialise the rank-zero A-copy-controlled tree
invariant. This is not an extra hypothesis of the published theorem.

When there is no A ↪ B, the Ramsey property of B for A is vacuous.
Choose C=B itself; its graph is a one-copy strict relational B-tree at
every rank, and the Ramsey arrow D → (B)^A provides a full embedding
B ↪ D as the protected projection.

This removes only a vacuity assumption from the DIRECT native iterated
functional theorem. No recursive/induced Ramsey proof is duplicated.
The strict full FUNCTION-tree target is still not asserted.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Direct native functional n-pass Ramsey iteration, including the
no-A-copy case. All clauses use actual function structures and the
original 2019 partial homomorphism-embedding convention; only the
local tree target is an induced *relational function-graph* tree. -/
theorem inducedRamsey_nativeFunctionalIteration_originalPartial_all
    (K : StructureClass (L := L))
    (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      RelStructure.LocallyTreeLike A.graph B.graph C.graph n ∧
      (∀ (S : Finset W), S.card ≤ n →
        ∀ (hS : C.IsClosed (↑S : Set W)),
          RelStructure.HasTreeCompletion B.graph
            (C.induce (↑S : Set W) hS).graph) ∧
      ∃ p : W → P,
        IsOriginalPartialHomomorphismEmbedding C D p := by
  classical
  by_cases hAB : Nonempty (Embedding A B)
  · exact inducedRamsey_nativeFunctionalIteration_originalPartial
      K hK A B D hKA hKB hpos κ hRamsey hA
      (Classical.choice hAB) n hn
  · obtain ⟨β, _⟩ :=
      hRamsey (fun _ => Classical.choice
        (inferInstance : Nonempty κ))
    have hSelf : Arrow A B B κ := by
      intro χ
      refine ⟨Embedding.id B, ?_⟩
      intro e _
      exact (hAB ⟨e⟩).elim
    have hLocal :
        RelStructure.LocallyTreeLike A.graph B.graph B.graph n :=
      FunctionalPartite.EHN.base_weakGraphLocallyTreeLike A B n
    let hWeak : WeakLocallyTreeCompletable B B n :=
      RelStructure.LocallyTreeCompletable.of_locallyTreeLike hLocal
    refine ⟨V, inferInstance, B, hKB, hSelf, hLocal, ?_,
      β, β.isEHNHomomorphismEmbedding.toOriginalPartial⟩
    intro S hCard hClosed
    exact hWeak.closedTest_graphCompletion S hCard hClosed

end StructuralRamsey.Structure

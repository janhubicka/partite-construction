import PartiteConstruction.Functional.PublishedSparseningScope
import PartiteConstruction.Functional.UnaryEHNCompletion
import PartiteConstruction.Functional.ProjectedClosedTreePullback

/-! # Functional sparsening in languages with unary functions

The original published Appendix A theorem requires a FULL
homomorphism-embedding back to the original Ramsey witness.
For unary set-valued functions, the genuine-function native EHN projection
is already a full homomorphism-embedding:
`IsEHNHomomorphismEmbedding.toFull_of_unary`.

Consequently the class-preserving weak-graph sparsening theorem in
`PublishedSparseningScope` proves the full projection clause in this
special case. The strict target tree clause is not automatic, but if
the original Ramsey witness is itself locally completable into strict
full function-language B-trees, the fully projected images of closed
small tests are closed and the verified closed-image pullback yields
the strict conclusion for the constructed in-class Ramsey witness.

The extension of arbitrary irreducible substructures of the final witness
to copies of B remains a separate, unproved functional obligation.
Neither theorem below asserts the full three-clause published theorem. -/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {U V P : Type v}

/-- Under unary function arities, the published FULL global
homomorphism-embedding clause (1) is recovered, together with all the
checked class-preserving weak graph-tree local conclusions. -/
theorem sparseningRamsey_unary_fullProjection_inClass
    (K : StructureClass (L := L))
    (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    (C₀ : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B C₀ κ)
    (hUnary : L.UnaryFuncArity)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      (∃ p : W → P, C.IsHomomorphismEmbedding C₀ p) ∧
      WeakLocallyTreeCompletable B C n ∧
      (∀ S : Finset W, S.card ≤ n →
        ∀ hS : C.IsClosed (↑S : Set W),
          RelStructure.HasTreeCompletion B.graph
            (C.induce (↑S : Set W) hS).graph) := by
  have hpos : L.PositiveFuncArity := by
    intro F
    rw [hUnary F]
    decide
  obtain ⟨W, hW, C, hMem, hRamsey, ⟨p, hp⟩, hWeak, hClosed⟩ :=
    sparseningRamsey_functionalWeakGraph_inClass
      K hK A B C₀ hKA hKB κ hArrow hpos hA n
  exact ⟨W, hW, C, hMem, hRamsey,
    ⟨p, hp.toFull_of_unary hUnary⟩, hWeak, hClosed⟩

/-- In the unary case, if the original Ramsey witness itself has
strict functional tree completions on n-vertex closed tests, the newly
constructed witness in the prescribed free-amalgamation class also has
full-function strict B-tree completions at exactly the same vertex rank.
This recovers published clauses (1) and (2), but not clause (3), under
the explicit extra local-tree assumption on the original witness. -/
theorem sparseningRamsey_unary_strictIfOriginalLocallyCompletable
    (K : StructureClass (L := L))
    (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    (C₀ : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B C₀ κ)
    (hUnary : L.UnaryFuncArity)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ)
    (hD : LocallyClosedTreeCompletable B C₀ n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      ∃ p : W → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        LocallyClosedTreeCompletable B C n := by
  classical
  obtain ⟨W, hW, C, hMem, hRamsey, ⟨p, hp⟩, _hWeak, _hClosed⟩ :=
    sparseningRamsey_unary_fullProjection_inClass
      K hK A B C₀ hKA hKB κ hArrow hUnary hA n
  refine ⟨W, hW, C, hMem, hRamsey, p, hp, ?_⟩
  intro S hSize hS
  have hpS :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding C₀
        (p ∘ Subtype.val) :=
    hp.comp (inclusion C (↑S : Set W) hS).isHomomorphismEmbedding
  have hImage : (S.image p).card ≤ n :=
    (Finset.card_image_le).trans hSize
  exact hD.pullback_localFull_closedImage p S hS hpS hImage

end StructuralRamsey.Structure

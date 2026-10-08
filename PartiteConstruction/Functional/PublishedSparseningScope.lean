import PartiteConstruction.Functional.EHNClosedTestGraphCorollary

/-! # The checked functional fragment of the published sparsening statement

The published Appendix A theorem is in a language with genuine set-valued
functions and asks for three simultaneous conclusions:
(1) a FULL homomorphism-embedding back to the original Ramsey witness,
(2) completions of bounded genuine closed substructures into STRICT FULL
    function-language trees of B-copies, and
(3) extension of each irreducible substructure to a B-copy.

The verified native EHN iteration currently supplies a full
function-language Ramsey arrow, a WEAK EHN projection, and bounded
weak-graph completions into strict RELATIONAL trees of B-function graphs.
The image of every weak test is taken WEAKLY on exactly the projected
vertices; no function-generated hull is charged to the size induction.

This file removes the auxiliary free-amalgamation-class parameter and the
separate A -> B assumption, and allows all finite vertex bounds. It is a
precise theorem in the original functional syntax which exposes exactly
what is currently proved. It does not silently strengthen any of the three
published conclusions. -/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {U V P : Type v}

/-- All finite structures form a free-amalgamation class. This lets us run
the genuine functional induced partite construction without making class
membership an additional theorem hypothesis. -/
private def unrestrictedClass : StructureClass (L := L) :=
  fun _ => True

private theorem unrestrictedClass_free :
    FreeAmalgamationClass (unrestrictedClass (L := L)) where
  hereditary := by
    intro V W A B _ _
    trivial
  free := by
    intro H E F C D A B Cstr sA sB iA iB _ _ _
    trivial

/-- A version in the published functional language, with every size bound
including zero, preserving the Ramsey arrow for FULL embeddings.

Property (1) is at present the EHN WEAK projection, not a full map.
Property (2) is a strict TREE OF FUNCTION GRAPHS and applies to arbitrary
weak tests; closed tests inherit it without enlarging the vertex set.
Property (3) of the published theorem is NOT asserted. -/
theorem sparseningRamsey_functionalWeakGraph
    (A : Structure L U) (B : Structure L V)
    (C₀ : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B C₀ κ)
    (hpos : L.PositiveFuncArity)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      Arrow A B C κ ∧
      (∃ p : W → P, C.IsEHNHomomorphismEmbedding C₀ p) ∧
      WeakLocallyTreeCompletable B C n ∧
      (∀ S : Finset W, S.card ≤ n →
        ∀ hS : C.IsClosed (↑S : Set W),
          RelStructure.HasTreeCompletion B.graph
            (C.induce (↑S : Set W) hS).graph) := by
  classical
  by_cases hAB : Nonempty (Embedding A B)
  · let K : StructureClass (L := L) := unrestrictedClass
    have hK : FreeAmalgamationClass K :=
      unrestrictedClass_free (L := L)
    obtain ⟨W, hW, C, _hmem, hArrowC, hWeak, _hClosed, p, hp⟩ :=
      inducedRamsey_directFunctional_closedGraphTests
        K hK A B C₀ trivial trivial hpos κ hArrow
        hA (Classical.choice hAB) (n + 1) (by omega)
    have hWeakN : WeakLocallyTreeCompletable B C n :=
      hWeak.mono (Nat.le_succ n)
    refine ⟨W, hW, C, hArrowC, ⟨p, hp⟩, hWeakN, ?_⟩
    intro S hCard hS
    exact hWeakN.closedTest_graphCompletion S hCard hS
  · obtain ⟨β, _⟩ :=
      hArrow (fun _ => Classical.choice
        (inferInstance : Nonempty κ))
    have hSelf : Arrow A B B κ := by
      intro χ
      refine ⟨Embedding.id B, ?_⟩
      intro e _
      exact (hAB ⟨e⟩).elim
    have hWeak : WeakLocallyTreeCompletable B B n :=
      RelStructure.LocallyTreeCompletable.of_homEmbedding_to_base
        id (RelStructure.Embedding.id B.graph).isHomomorphismEmbedding n
    refine ⟨V, inferInstance, B, hSelf,
      ⟨β, β.isEHNHomomorphismEmbedding⟩, hWeak, ?_⟩
    intro S hCard hS
    exact hWeak.closedTest_graphCompletion S hCard hS

end StructuralRamsey.Structure

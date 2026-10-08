import PartiteConstruction.Functional.EHNIteratedWeakTree
import PartiteConstruction.Iterated.WeakFunctionalTreeCompletion

/-! # Genuine closed tests from the native functional weak-size induction

The direct genuine-function iterated EHN construction controls arbitrary weak
vertex tests, with no function-closure hull taken when measuring their size.

A genuine substructure is already a weak substructure of exactly the same
finite vertex set. Thus every *function-closed* test on at most n vertices
inherits a homomorphism-embedding of its function graph into a relational
tree amalgam of B-graphs. This is the precise consequence relevant to the
printed local-size phrasing.

The target is still a relational graph-tree: no assertion is made that its
gluing roots are function-closed or its completion map reflects complete
target function fibres. Those stronger certificates would be needed to
obtain a genuine full function-language tree completion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Direct functional sparsening, stated simultaneously for weak tests and
genuine closed tests on the *same number of vertices*. The Ramsey arrow and
the global EHN projection remain in the genuine function language. -/
theorem inducedRamsey_directFunctional_closedGraphTests
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A B C κ ∧
      WeakLocallyTreeCompletable B C n ∧
      (∀ (S : Finset W), S.card ≤ n →
        ∀ (hS : C.IsClosed (↑S : Set W)),
          RelStructure.HasTreeCompletion B.graph
            (C.induce (↑S : Set W) hS).graph) ∧
      ∃ p : W → P, C.IsEHNHomomorphismEmbedding D p := by
  obtain ⟨W, hW, C, hC, hArrow, hLocal, p, hp⟩ :=
    inducedRamsey_directFunctionalWeakGraph
      K hK A B D hKA hKB hpos κ hRamsey hA eAB n hn
  let hWeak : WeakLocallyTreeCompletable B C n :=
    RelStructure.LocallyTreeCompletable.of_locallyTreeLike hLocal
  refine ⟨W, hW, C, hC, hArrow, hWeak, ?_, p, hp⟩
  intro S hCard hClosed
  exact hWeak.closedTest_graphCompletion S hCard hClosed

end StructuralRamsey.Structure

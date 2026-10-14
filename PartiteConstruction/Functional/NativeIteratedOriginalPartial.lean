import PartiteConstruction.Functional.EHNClosedTestGraphCorollary
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Already verified native functional iteration, in the 2019 partial semantics

This theorem does not redo any recursive/induced partite construction.
It reuses the completed native EHN n-pass functional theorem verbatim.

The only repackaging is semantic: the composed native EHN projection
is precisely the ORIGINAL 2019 partial-function homomorphism-embedding,
which preserves entire output fibres at DEFINED source inputs but does
not reflect undefined source inputs.

All stages remain genuine set-valued-function structures. Exact weak
vertex tests give controlled relational graph-tree witnesses, and genuine
function-closed tests inherit those graph witnesses at the same vertex
bound. A strict FULL function-language B-tree target remains a separate
mixed-root compatibility obligation; no such target is asserted.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- An n-pass genuine native functional Ramsey construction, formulated
with the original 2019 partial-function homomorphism-embedding.
The locally tree-like component keeps the A-copy control, rather than
only the weaker unlabelled completion statement. -/
theorem inducedRamsey_nativeFunctionalIteration_originalPartial
    (K : StructureClass (L := L))
    (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Embedding A B)
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
  obtain ⟨W, hW, C, hKC, hArrow, hLocal, p, hp⟩ :=
    inducedRamsey_directFunctionalWeakGraph
      K hK A B D hKA hKB hpos κ hRamsey hA eAB n hn
  let hWeak : WeakLocallyTreeCompletable B C n :=
    RelStructure.LocallyTreeCompletable.of_locallyTreeLike hLocal
  refine ⟨W, hW, C, hKC, hArrow, hLocal, ?_, p,
    hp.toOriginalPartial⟩
  intro S hCard hClosed
  exact hWeak.closedTest_graphCompletion S hCard hClosed

end StructuralRamsey.Structure

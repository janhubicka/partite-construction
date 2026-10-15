import PartiteConstruction.Functional.WeakSingletonPartialProjection
import PartiteConstruction.Functional.NativeIteratedFinalBCover
import PartiteConstruction.Ramsey.AllThosePartialFiniteModels

/-!
# Actual native singleton-functional n-pass with exact weak projection

The recursive rank reduction produces singleton-valued partial functions.
The original-partial model class is already proved hereditary and
free-amalgamating, including the nullary-root case; the previously
proved native functional EHN passes preserve *membership in that class*.
Thus NO new functional operation with multiple outputs occurs in an
iterated Picture.

Specialize the previously proved n-pass + final B-coverage theorem to
that class, and add the exact source-defined weak-fibre projection law
from `WeakSingletonPartialProjection.lean` on EVERY weak vertex set.

This is still a strict RELATIONAL graph-tree locality assertion, not
the outstanding strict full-functional B-tree completion theorem.
The actual strict mixed-root relative extension remains open.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A completely native function-language n-pass sparsening witness
with no newly multivalued intermediate operation. Every exact weak
source/image pair has *both* the original partial defined-fibre
homomorphism and the weak graph homomorphism-embedding.

The original recursive Ramsey witness D is an ordinary function
structure; it is not required to be an element of the singleton
free-amalgamation class. Only A and B are singleton-valued.

Local tree targets are still RELATIONAL B-graphs, not as yet genuine
strict function-language B-trees. -/
theorem sparseningRamsey_nativeSingleton_graphStrict_weakProjection
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hASingle : A.SingletonValued)
    (hBSingle : B.SingletonValued)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hAgraph : A.graph.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      C.SingletonValued ∧
      Arrow A B C κ ∧
      RelStructure.LocallyTreeLike A.graph B.graph C.graph n ∧
      IrreduciblesExtendTo B C ∧
      ∃ p : W → P,
        IsOriginalPartialHomomorphismEmbedding C D p ∧
        ∀ S : Set W,
          (IsOriginalPartialHomomorphism
            (C.weakInduce S) (D.weakInduce (p '' S))
            (fun x : S =>
              (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S))) ∧
          (C.weakInduce S).IsWeakHomomorphismEmbedding
            (D.weakInduce (p '' S))
            (fun x : S =>
              (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  classical
  obtain ⟨W, hW, C, hCSingle, hArrow, ⟨p, hp⟩,
      hGraphTree, hCover, _hLoose, _hClosedTests⟩ :=
    sparseningRamsey_nativeFunctional_graphStrict_withBCover
      (originalPartialModelClass (L := L))
      (originalPartialModelClass_free (L := L))
      A B D hASingle hBSingle hpos κ hRamsey hAgraph n hn
  refine ⟨W, hW, C, hCSingle, hArrow, hGraphTree, hCover,
      p, hp, ?_⟩
  intro S
  exact hp.toEHN.weakImage_singleton hCSingle S

end StructuralRamsey.Structure

import PartiteConstruction.Functional.NativeIteratedFinalBCover

/-!
# Class-free form of corrected published functional weak sparsening

The author-supplied published theorem does not assume a designated
free-amalgamation subclass. The completed native n-pass theorem can also
be stated for the full class of finite structures, by instantiating its
free-amalgamation class parameter with the universal class.

This drops only the unnecessary extra CLASS hypothesis; it does not weaken
the honest distinctions between the original 2019 partial-function global
projection, strict relational function-GRAPH local B-trees, and the still-open
strict full-FUNCTION local B-tree conclusion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Class-free corrected functional sparsening: full Ramsey arrow, 2019
partial-function projection, exact weak-vertex graph-tree tests, and actual
B-copy extension for every full irreducible. -/
theorem sparseningRamsey_nativeFunctional_graphStrict_withBCover_unrestricted
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      Arrow A B C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      RelStructure.LocallyTreeLike A.graph B.graph C.graph n ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B W C := by
  let K : StructureClass (L := L) := fun _ => True
  have hK : FreeAmalgamationClass K := {
    hereditary := by intro V W A B hB e; trivial
    free := by intro H E F C D A B Cstr sA sB iA iB hA hB hfree; trivial
  }
  obtain ⟨W, hW, C, _hMem, hArrow, hProj, hTree, hCover, hLoose, _⟩ :=
    sparseningRamsey_nativeFunctional_graphStrict_withBCover
      K hK A B D trivial trivial hpos κ hRamsey hA n hn
  exact ⟨W, hW, C, hArrow, hProj, hTree, hCover, hLoose⟩

end StructuralRamsey.Structure

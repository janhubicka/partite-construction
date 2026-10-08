import PartiteConstruction.Functional.PublishedSparseningLoose
import PartiteConstruction.Functional.UnaryEHNCompletion

/-! # Unary functions: only the strict-root condition needs weakening

For unary functions every EHN weak homomorphism-embedding is full.
Combining this fact with the completed all-arity loose-tree construction
recovers the original full global projection and irreducible B-extension,
with full embeddings of all closed local tests into genuine loose trees.

This corollary has no hereditary graph-irreducibility assumption and does
not assume that the input witness already has a local-tree property.
It does not assert the original STRICT tree conclusion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- All published types of conclusions for unary functions, weakening
only the tree's irreducible-root-container requirement. -/
theorem sparseningRamsey_unary_looseFullTrees_inClass
    (K : StructureClass (L := L)) (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hB : K B) (hUnary : L.UnaryFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B D κ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧ Arrow A B C κ ∧
      (∃ p : W → P, C.IsHomomorphismEmbedding D p) ∧
      LooseTreeAmalgam B W C ∧ IrreduciblesExtendTo B C ∧
      ∀ n : ℕ, LocallyClosedLooseTreeEmbeddable B C n := by
  obtain ⟨W, hW, C, hMem, hRamsey, ⟨p, hp⟩, hTree, hExt, hLocal⟩ :=
    sparseningRamsey_functional_looseFullTrees_inClass
      K hK A B D hA hB κ hArrow
  exact ⟨W, hW, C, hMem, hRamsey,
    ⟨p, hp.toFull_of_unary hUnary⟩, hTree, hExt, hLocal⟩

/-- Class-free unary version, with full global and local maps and final
B-copy extension. Only the tree is loose rather than strict. -/
theorem sparseningRamsey_unary_looseFullTrees
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hUnary : L.UnaryFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B D κ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      Arrow A B C κ ∧
      (∃ p : W → P, C.IsHomomorphismEmbedding D p) ∧
      LooseTreeAmalgam B W C ∧ IrreduciblesExtendTo B C ∧
      ∀ n : ℕ, LocallyClosedLooseTreeEmbeddable B C n := by
  obtain ⟨W, hW, C, hRamsey, ⟨p, hp⟩, hTree, hExt, hLocal⟩ :=
    sparseningRamsey_functional_looseFullTrees A B D κ hArrow
  exact ⟨W, hW, C, hRamsey,
    ⟨p, hp.toFull_of_unary hUnary⟩, hTree, hExt, hLocal⟩

end StructuralRamsey.Structure

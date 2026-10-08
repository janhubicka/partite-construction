import PartiteConstruction.Functional.EHNProjectedCoverAllArity
import PartiteConstruction.Functional.ProjectedLooseCompletion

/-! # A corrected full-function alternative to the published sparsening theorem

All Ramsey embeddings, free amalgams, local embeddings, and final B-copy
extensions remain in the genuine function language, with arbitrary arities
including constants. Two changes from the literal published statement are
explicit: the global projection is EHN weak, and the functional B-tree has
arbitrary closed gluing roots (the loose notion).

One native induced pass followed by full free-decomposition completion
suffices. The entire final witness is a finite loose B-tree, so all closed
local tests fully embed into such a tree. This is not a strict n-pass
sparsening theorem, and does not redefine the published strict tree notion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Genuine functional Ramsey witnesses with weak projected maps, full
loose-tree targets, and the original irreducible-extension conclusion.
No arity, irreducibility or graph-irreducibility assumption is used. -/
theorem sparseningRamsey_functional_looseFullTrees_inClass
    (K : StructureClass (L := L)) (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B D κ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧ Arrow A B C κ ∧
      (∃ p : W → P, C.IsEHNHomomorphismEmbedding D p) ∧
      LooseTreeAmalgam B W C ∧ IrreduciblesExtendTo B C ∧
      ∀ n : ℕ, LocallyClosedLooseTreeEmbeddable B C n := by
  obtain ⟨S, hCov, hRamsey⟩ :=
    FunctionalPartite.EHN.inducedConstruction_allArity_projectedCover
      hK A B D hA hB κ hArrow
  letI : Finite S.Carrier := S.finiteCarrier
  have hCovS : ProjectsIrreduciblesInto B S.system.toStructure D S.system.part := hCov
  obtain ⟨W, hW, C, hTree, e, p, hp, _hCommute⟩ :=
    hCovS.projectedLooseCompletion S.isPartite
  have hMem : K C := hTree.mem_freeAmalgamationClass hK hB
  have hArrowC : Arrow A B C κ := by
    intro χ
    obtain ⟨f, hf⟩ := hRamsey (fun g => χ (e.comp g))
    exact ⟨e.comp f, fun g₁ g₂ => hf g₁ g₂⟩
  refine ⟨W, hW, C, hMem, hArrowC, ⟨p, hp⟩,
    hTree, hTree.irreduciblesExtendTo, ?_⟩
  intro n S _hSize hS
  exact ⟨W, C, hTree, ⟨inclusion C (↑S : Set W) hS⟩⟩

/-- Class-free form for every relation/function language, using an EHN
weak global projection and genuine loose full-function B-tree targets. -/
theorem sparseningRamsey_functional_looseFullTrees
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B D κ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      Arrow A B C κ ∧
      (∃ p : W → P, C.IsEHNHomomorphismEmbedding D p) ∧
      LooseTreeAmalgam B W C ∧ IrreduciblesExtendTo B C ∧
      ∀ n : ℕ, LocallyClosedLooseTreeEmbeddable B C n := by
  let K : StructureClass (L := L) := fun _ => True
  have hK : FreeAmalgamationClass K := {
    hereditary := by intro V W A B hB e; trivial
    free := by intro H E F C D A B Cstr sA sB iA iB hA hB hfree; trivial
  }
  obtain ⟨W, hW, C, _hMem, hArrowC, hp, hTree, hExt, hLocal⟩ :=
    sparseningRamsey_functional_looseFullTrees_inClass
      K hK A B D trivial trivial κ hArrow
  exact ⟨W, hW, C, hArrowC, hp, hTree, hExt, hLocal⟩

end StructuralRamsey.Structure

import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Functional.GeneratedTreeCompletion

/-! # Pure-core completion from local domain reflection

For a closed test lying in a functional Hales--Jewett core, the EHN part
projection is already exact on every defined source fibre.  Thus the only
obstruction to completing the test inside one copy of the tree base is
reflection of function-domain nonemptiness.

This file packages that implication.  The remaining pure-core work in the
functional sparsening proof is therefore entirely a domain-reflection problem.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P V W : Type v}
variable {A : Structure L P}
variable {Base : Structure L V}
variable {E : System L P W}

/-- A closed test in an EHN-partite functional system maps fully into one
Base-copy as soon as function domains reflect on that test. -/
theorem pureCore_oneCopy_of_domainReflection
    (hE : E.WeaklyPartiteOver A)
    (eAB : Structure.Embedding A Base)
    (S : Finset W)
    (hS : E.toStructure.IsClosed (↑S : Set W))
    (hreflect :
      ∀ F (x : Fin (L.funcArity F) → ↥(↑S : Set W)),
        (A.func F ((E.part ∘ Subtype.val) ∘ x)).Nonempty →
          ((E.toStructure.induce (↑S : Set W) hS).func F x).Nonempty) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        Structure.IsHomomorphismEmbedding
          (E.toStructure.induce (↑S : Set W) hS) Target f := by
  have hpS :
      Structure.IsHomomorphismEmbedding
        (E.toStructure.induce (↑S : Set W) hS)
        A (E.part ∘ Subtype.val) :=
    StructuralRamsey.Structure.IsEHNHomomorphismEmbedding.restrictClosed_toFull_of_domainReflection
      hE (↑S : Set W) hS hreflect
  let f : ↥(↑S : Set W) → V :=
    eAB ∘ (E.part ∘ Subtype.val)
  have hf :
      Structure.IsHomomorphismEmbedding
        (E.toStructure.induce (↑S : Set W) hS) Base f := by
    exact StructuralRamsey.Structure.IsHomomorphismEmbedding.comp
      eAB.isHomomorphismEmbedding hpS
  have hTree : TreeAmalgam Base V Base :=
    StructuralRamsey.Structure.TreeAmalgam.copy
      (Structure.Embedding.id Base) (by
      intro b
      exact ⟨b, rfl⟩)
  exact ⟨V, Base, hTree, f, hf⟩

end StructuralRamsey.FunctionalPartite

import PartiteConstruction.Functional.WeakBareOnePassAllArityControlBudget
import PartiteConstruction.Functional.WeakBareFinalBCoverFromRankedStage

/-!
# Track D: complete CONDITIONAL strict full-functional sparsening endgame

English proof FIRST:
docs/track-d-english-conditional-strict-full-bcover-endgame-20261115.md

A true full-functional Ramsey control D with independent
AtMostBare rank F_A(m) gives one genuine all-arity native EHN
Ramsey pass at rank m+1. The separately proposed final
internal B-copy extension is then applied to that SAME stage;
EHN pullback retains strict FULL-functional local targets
despite the final C itself being only a loose B-tree.

This packages the exact Ramsey arrow, internal B-copy coverage,
original-2019 source-defined partial global projection, genuine
strict functional weak-test locality and closed-test completions
on ONE final witness C.

The enlarged rank of D remains an independent hypothesis.
The theorem does NOT give an unconditional n-pass construction
or assert a false total-fibre global projection. A is irreducible.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A complete single-witness strict functional sparsening theorem
CONDITIONAL on a jointly high-rank and full-Ramsey control D.

All arities including nullary functions are allowed. No weak
source test or its exact part image is inflated by closure.
The final C is a loose full-functional B-tree with every
irreducible extending into an INTERNAL B-copy; each literal
weak n-test nevertheless has a STRICT full-functional B-tree
target and each truly closed test has genuine original-2019
partial strict tree completion.

The extra rank F_A(m) on D and A.Irreducible are explicitly
retained; this is not the unrestricted published theorem. -/
theorem sparseningRamsey_bareStrict_withBCover_of_controlBudget
    (K : StructureClass (L := L)) (hK : FreeAmalgamationClass K)
    (A : Structure L U) [Fintype U]
    (hKA : K A) (hA : A.Irreducible)
    (B : Structure L V) [Finite V]
    (hKB : K B) (hB : B.Irreducible)
    (eAB : Embedding A B)
    (D : Structure L P) [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Arrow A B D κ)
    (m : ℕ)
    (hBudget :
      SetAmbientRelativeWeakTreeWitness.AtMostBare B D
        (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := U) m)) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      (∃ p : W → P,
        IsOriginalPartialHomomorphismEmbedding C D p) ∧
      SetAmbientRelativeWeakTreeWitness.AtMostBare B C (m + 1) ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B W C ∧
      (∀ S : Finset W, S.card ≤ m + 1 →
        ∀ hClosed : C.IsClosed (↑S : Set W),
          HasOriginalPartialTreeCompletion
            B (C.induce (↑S : Set W) hClosed)) := by
  classical
  obtain ⟨T, hBareT, hArrowT⟩ :=
    FunctionalPartite.EHN.inducedConstruction_allArity_bareRank_of_controlBudget
      hK A hKA hA B hKB hB eAB D κ hArrow m hBudget
  exact sparseningRamsey_bareRank_withBCover_of_stage
    K hK A B D hKA hKB κ T hArrowT (m + 1) hBareT

end StructuralRamsey.Structure

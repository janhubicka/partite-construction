import PartiteConstruction.Functional.WeakBareEHNPullback
import PartiteConstruction.Functional.WeakBareClosedOriginalPartialCompletion
import PartiteConstruction.Functional.LooseTreeAmalgam
import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.ProjectedLooseCompletion

/-!
# Track D: unconditional strict native no-A-copy case

English proof FIRST:
docs/track-d-english-unconditional-vacuous-a-strict-native-20261115.md

When no full A embeds into B, the Ramsey arrow of B for A is
vacuous. A given genuine A/B Ramsey control D nevertheless
contains a full B copy (from the constant colouring). Taking
C = B gives the actual full original-partial projection to D,
a one-copy STRICT full-functional B-tree on C at every bound,
internal B-copy coverage and strict original-2019 completion
of each literal closed weak test.

Unlike the mixed-rank route this requires NO irreducibility
of A or B, no function-arity restriction and no extra control rank.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Unconditional all-arity strict full-functional sparsening
when there is no genuine FULL A→B embedding.

The SAME final C has the genuine full Ramsey arrow, internal
B-copy cover, global original-2019 partial projection and
strict full-functional local trees on every exact weak n-test
(and on every actual closed test at the same rank). The entire
C is a strict one-copy B-tree. This covers only the vacuous
A↪B branch, not the nonvacuous mixed rank induction. -/
theorem sparseningRamsey_bareStrict_noACopy
    (K : StructureClass (L := L))
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hNoAB : ¬ Nonempty (Embedding A B))
    (n : ℕ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      (∃ p : W → P,
        IsOriginalPartialHomomorphismEmbedding C D p) ∧
      SetAmbientRelativeWeakTreeWitness.AtMostBare B C n ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B W C ∧
      (∀ S : Finset W, S.card ≤ n →
        ∀ hClosed : C.IsClosed (↑S : Set W),
          HasOriginalPartialTreeCompletion
            B (C.induce (↑S : Set W) hClosed)) := by
  classical
  obtain ⟨beta, _hbeta⟩ :=
    hRamsey (fun _ => Classical.choice
      (inferInstance : Nonempty κ))
  have hSelfArrow : Arrow A B B κ := by
    intro χ
    refine ⟨Embedding.id B, ?_⟩
    intro e₁ _e₂
    exact (hNoAB ⟨e₁⟩).elim
  have hTree : TreeAmalgam B V B :=
    TreeAmalgam.copy (Embedding.id B) (fun b => ⟨b, rfl⟩)
  have hBare : SetAmbientRelativeWeakTreeWitness.AtMostBare B B n :=
    SetAmbientRelativeWeakTreeWitness.AtMostBare.of_strictTree hTree n
  have hLoose : LooseTreeAmalgam B V B :=
    LooseTreeAmalgam.ofTree hTree
  have hCover : IrreduciblesExtendTo B B :=
    hLoose.irreduciblesExtendTo
  have hProj : IsOriginalPartialHomomorphismEmbedding B D beta :=
    beta.isEHNHomomorphismEmbedding.toOriginalPartial
  refine ⟨V, inferInstance, B, hKB, hSelfArrow,
    ⟨beta, hProj⟩, hBare, hCover, hLoose, ?_⟩
  intro S hSize hClosed
  exact
    SetAmbientRelativeWeakTreeWitness.AtMostBare.closedTest_originalPartialCompletion
      n hBare S hSize hClosed

end StructuralRamsey.Structure

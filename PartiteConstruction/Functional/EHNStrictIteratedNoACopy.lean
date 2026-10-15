import PartiteConstruction.Functional.EHNOriginalPartialMaximalMixedFromTwo
import PartiteConstruction.Functional.EHNNativeOriginalPartialRankOneAll

/-!
# Strict original-2019 functional n-pass sparsening without A ↪ B

The genuine full-functional n-pass theorem is Lean verified conditional
on maximal mixed-root relative extensions when A embeds into B.
This embedding is an initialization convenience, not a hypothesis of
the published Ramsey statement.

If A does not embed into B, every B-copy is trivially monochromatic
for A. Take C = B itself. The original input Ramsey arrow supplies
a full embedding β : B ↪ D to serve as the global original-2019
partial homomorphism-embedding. B is a strict one-copy full-functional
B-tree, so every genuine function-closed test of B strictly completes
for ANY vertex-size bound n. All irreducibles extend to the actual
B-copy C itself.

Thus the conditional full n-pass strict functional refinement requires
no artificial A ↪ B assumption. The higher rank maximal mixed-root
schema remains a genuine OPEN mathematical condition in the other case,
and the survey's stronger total-fibre global map is not asserted.
-/

namespace StructuralRamsey.FunctionalPartite.EHN.StrictRanked

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V P : Type v}

/-- Full conditional strict original-2019 native n-pass Ramsey and final
B-cover, with NO A↪B hypothesis. For an actual A↪B we require the
already verified rank≥2 maximal mixed-root extension schema. With no
A↪B, the condition is vacuous and the literal B-copy is sufficient. -/
theorem sparsening_of_maximal_mixed_schema_from_two_all
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hMixed : ∀ _eAB : Structure.Embedding A Base,
      MaximalMixedSchemaFromTwo K A Base)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A Base C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      LocallyClosedOriginalPartialTreeCompletable Base C n ∧
      IrreduciblesExtendTo Base C ∧
      LooseTreeAmalgam Base W C := by
  classical
  by_cases hAB : Nonempty (Structure.Embedding A Base)
  · let eAB : Structure.Embedding A Base := Classical.choice hAB
    exact sparsening_of_maximal_mixed_schema_from_two
      K hK A Base D hKA hKB hBIrr hPos eAB
      κ hArrow (hMixed eAB) n hn
  · obtain ⟨beta, _⟩ :=
      hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    have hSelf : Structure.Arrow A Base Base κ := by
      intro χ
      refine ⟨Structure.Embedding.id Base, ?_⟩
      intro e _
      exact (hAB ⟨e⟩).elim
    have hTree : TreeAmalgam Base V Base :=
      TreeAmalgam.copy (Structure.Embedding.id Base)
        (fun x => ⟨x, rfl⟩)
    have hLocal : LocallyClosedOriginalPartialTreeCompletable
        Base Base n := by
      intro S _ hS
      let e : Structure.Embedding
          (Base.induce (↑S : Set V) hS) Base :=
        Structure.inclusion Base (↑S : Set V) hS
      exact ⟨V, Base, hTree, e,
        e.isEHNHomomorphismEmbedding.toOriginalPartial⟩
    have hLoose : LooseTreeAmalgam Base V Base :=
      LooseTreeAmalgam.copy (Structure.Embedding.id Base)
        (fun x => ⟨x, rfl⟩)
    have hCover : IrreduciblesExtendTo Base Base :=
      hLoose.irreduciblesExtendTo
    exact ⟨V, inferInstance, Base, hKB, hSelf,
      ⟨beta, beta.isEHNHomomorphismEmbedding.toOriginalPartial⟩,
      hLocal, hCover, hLoose⟩

end StructuralRamsey.FunctionalPartite.EHN.StrictRanked

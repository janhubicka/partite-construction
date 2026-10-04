import PartiteConstruction.Iterated.CliqueExpansion
import PartiteConstruction.Iterated.SparseningUniformFinal

/-! # Strict reducts when the base is irreducible

For a strict tree amalgam in the complete-graph expansion, each gluing-root
image lies in an irreducible expanded substructure.  That irreducible
substructure lies inside one constituent base copy.  If the reduct of the
base itself is irreducible, the same base copy supplies the irreducible
container after forgetting the complete relation.

Consequently the clique-expansion argument yields the survey's strict
property-(2) tree completions whenever B is irreducible, with no
irreducibility assumption on A.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

namespace TreeAmalgam

/-- A strict expanded tree remains strict after clique reduct when the base
reduct is irreducible. -/
theorem cliqueReduct_strict
    {Base : RelStructure L.withClique V}
    {T : RelStructure L.withClique W}
    (hBase : Base.cliqueReduct.Irreducible)
    (hT : TreeAmalgam Base W T) :
    TreeAmalgam Base.cliqueReduct W T.cliqueReduct := by
  induction hT with
  | copy h =>
      exact .copy h.cliqueReduct
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      have hc₁r : f₁.cliqueReduct.ContainedInIrreducible := by
        rcases hc₁ with ⟨S, hS, hsub⟩
        let inc : Embedding (T₁.induce S) T₁ := inclusion T₁ S
        obtain ⟨j, hj⟩ :=
          h₁.irreducible_contained_in_copy hS inc
        let jr : Embedding Base.cliqueReduct T₁.cliqueReduct :=
          j.cliqueReduct
        refine ⟨Set.range jr, hBase.range_embedding jr, ?_⟩
        intro d
        let z : S := ⟨f₁ d, hsub d⟩
        obtain ⟨b, hb⟩ := hj z
        refine ⟨b, ?_⟩
        exact hb.symm
      have hc₂r : f₂.cliqueReduct.ContainedInIrreducible := by
        rcases hc₂ with ⟨S, hS, hsub⟩
        let inc : Embedding (T₂.induce S) T₂ := inclusion T₂ S
        obtain ⟨j, hj⟩ :=
          h₂.irreducible_contained_in_copy hS inc
        let jr : Embedding Base.cliqueReduct T₂.cliqueReduct :=
          j.cliqueReduct
        refine ⟨Set.range jr, hBase.range_embedding jr, ?_⟩
        intro d
        let z : S := ⟨f₂ d, hsub d⟩
        obtain ⟨b, hb⟩ := hj z
        refine ⟨b, ?_⟩
        exact hb.symm
      exact .glue ih₁ ih₂
        f₁.cliqueReduct f₂.cliqueReduct hc₁r hc₂r
        i₁.cliqueReduct i₂.cliqueReduct hfree.cliqueReduct

end TreeAmalgam

/-- Forgetting the complete relation preserves strict local tree
completability when the base reduct is irreducible. -/
theorem LocallyTreeLike.cliqueReduct_strict
    {A : RelStructure L.withClique U}
    {B : RelStructure L.withClique V}
    {C : RelStructure L.withClique W}
    {n : ℕ}
    (hB : B.cliqueReduct.Irreducible)
    (h : LocallyTreeLike A B C n) :
    LocallyTreeCompletable B.cliqueReduct C.cliqueReduct n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, _⟩ := h S hS
  have hfr0 :
      (C.induce (↑S : Set W)).cliqueReduct.IsHomomorphismEmbedding
        T.cliqueReduct f :=
    hf.cliqueReduct
  have hfr :
      (C.cliqueReduct.induce (↑S : Set W)).IsHomomorphismEmbedding
        T.cliqueReduct f := by
    rw [← cliqueReduct_induce C (↑S : Set W)]
    exact hfr0
  exact ⟨Y, T.cliqueReduct,
    hTree.cliqueReduct_strict hB, f, hfr⟩

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- Full strict-tree sparsening when B is irreducible.  No irreducibility
hypothesis on A is required. -/
theorem sparseningRamsey_strict_baseIrreducible_all
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hB : B.Irreducible)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeCompletable B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  have hRamseyPlus :
      StructuralRamsey.Arrow
        A.withClique B.withClique C₀.withClique κ :=
    StructuralRamsey.arrow_withClique A B C₀ κ hRamsey
  obtain ⟨Z, hZ, Cplus, hArrowPlus,
      p, hpPlus, hLocalPlus, hExtPlus⟩ :=
    sparseningRamsey_uniformFinal_all
      A.withClique B.withClique C₀.withClique
      κ hRamseyPlus
      (RelStructure.withClique_hereditarilyIrreducible A) n
  let C : RelStructure L Z := Cplus.cliqueReduct
  have hArrow : StructuralRamsey.Arrow A B C κ :=
    StructuralRamsey.arrow_cliqueReduct A B Cplus κ hArrowPlus
  have hp : C.IsHomomorphismEmbedding C₀ p := by
    simpa [C] using hpPlus.cliqueReduct
  have hLocal : RelStructure.LocallyTreeCompletable B C n := by
    simpa [C] using hLocalPlus.cliqueReduct_strict hB
  have hExt : RelStructure.IrreduciblesExtendTo B C := by
    simpa [C] using hExtPlus.cliqueReduct
  exact ⟨Z, hZ, C, hArrow, p, hp, hLocal, hExt⟩

end StructuralRamsey.Partite.IteratedSparsening

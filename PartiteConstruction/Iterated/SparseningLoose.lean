import PartiteConstruction.Iterated.CliqueExpansion
import PartiteConstruction.Iterated.SparseningUniformFinal

/-! # Sparsening for the loose tree-amalgam notion

Expand every structure by a fresh complete irreflexive binary relation.
Induced embeddings are unchanged, while the expanded source is
hereditarily irreducible.  Apply the already verified strict-tree sparsening
theorem in the expansion, then forget the fresh relation.

After forgetting, strict tree amalgams become loose tree amalgams.  The
Ramsey arrow, homomorphism-embedding projection, and irreducible-extension
property all descend.

Thus the sparsening theorem for the older/cited loose tree-amalgam notion
requires no irreducibility hypothesis on A at all.
-/
namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- End-to-end sparsening for loose tree amalgams.  No irreducibility
hypothesis on A is required. -/
theorem sparseningRamsey_loose_all
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LooseLocallyTreeCompletable B C n ∧
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
  have hLocal : RelStructure.LooseLocallyTreeCompletable B C n := by
    simpa [C] using hLocalPlus.cliqueReduct_loose
  have hExt : RelStructure.IrreduciblesExtendTo B C := by
    simpa [C] using hExtPlus.cliqueReduct
  exact ⟨Z, hZ, C, hArrow, p, hp, hLocal, hExt⟩

end StructuralRamsey.Partite.IteratedSparsening

import PartiteConstruction.Iterated.SparseningIteration
import PartiteConstruction.Iterated.FinalSparsening

/-! # A checked strengthened sparsening theorem

This assembles the verified iterated induced construction with the verified
final finite attachment phase.  It proves the relational sparsening theorem
for positive \`n\` under the sufficient hereditary-irreducibility assumptions
identified by the formalization.

The output simultaneously has the Ramsey arrow, a homomorphism-embedding back
to the original Ramsey witness, the strengthened local-tree invariant, and the
property that every irreducible substructure extends to a copy of \`B\`.
-/
namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- End-to-end sparsening under hereditary irreducibility of both the control
structure and the base structure. -/
theorem sparseningRamsey_hereditarilyIrreducible
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hA : A.HereditarilyIrreducible)
    (hB : B.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding C₀ p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  classical
  obtain ⟨S, _⟩ :=
    build A B C₀ κ hRamsey hA eAB n hn
  letI : Fintype S.Vertex := Fintype.ofFinite S.Vertex
  obtain ⟨T, hExtend⟩ :=
    RelStructure.FinalSparsening.build_all
      A B S.C C₀ n S.projection
      hA eAB hB
      S.projectionHE S.locallyTreeLike S.projected
  have hArrow :
      StructuralRamsey.Arrow A B T.C κ :=
    RelStructure.FinalSparsening.Stage.arrow T S.arrow
  exact ⟨T.Vertex, inferInstance, T.C, hArrow,
    T.projection, T.projectionHE, T.locallyTreeLike, hExtend⟩

end StructuralRamsey.Partite.IteratedSparsening

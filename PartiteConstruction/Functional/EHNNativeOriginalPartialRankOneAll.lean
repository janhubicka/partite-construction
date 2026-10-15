import PartiteConstruction.Functional.EHNNativeOriginalPartialRankOne

/-!
# Rank-one strict original-partial functional sparsening WITHOUT A ↪ B

The published theorem does not require a prescribed embedding A into B.
The unconditional genuine native n=1 strict result of the previous
module uses A ↪ B in its non-vacuous induced Ramsey construction.

If there is no A ↪ B, every B-copy automatically satisfies the
A-Ramsey arrow. Take C=B itself. The input arrow D -> (B)^A_r
gives a full embedding β:B→D, so its original-partial projection is
genuine. Every closed test of B embeds back into B, which is a strict
one-copy B-tree. Every irreducible substructure is already contained
in the whole B-copy; in fact B is a loose tree of one copy.

Thus rank-one strict functional sparsening needs no A ↪ B assumption,
exactly as the published statement demands, under the same B
irreducibility and positive-function-arity hypotheses.

No total-fibre global projection or all-weak-test strict completion
is asserted. The higher-rank maximal mixed-root schema is independent.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Unconditional corrected original-2019 functional sparsening at rank 1
with no A→Base embedding assumption. The non-vacuous case uses the
fully verified native rank-one construction; the vacuous case simply
uses a genuine copy Base, projecting by Base ↪ D obtained from the
input Ramsey arrow. -/
theorem sparsening_originalPartial_strict_one_all
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A Base C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      LocallyClosedOriginalPartialTreeCompletable Base C 1 ∧
      IrreduciblesExtendTo Base C ∧
      LooseTreeAmalgam Base W C := by
  classical
  by_cases hAB : Nonempty (Structure.Embedding A Base)
  · exact sparsening_originalPartial_strict_one
      K hK A Base D hKA hKB hBIrr hPos
      (Classical.choice hAB) κ hArrow
  · obtain ⟨beta, _⟩ :=
      hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    have hSelf : Structure.Arrow A Base Base κ := by
      intro chi
      refine ⟨Structure.Embedding.id Base, ?_⟩
      intro e _
      exact (hAB ⟨e⟩).elim
    have hTree : TreeAmalgam Base V Base :=
      TreeAmalgam.copy (Structure.Embedding.id Base)
        (fun b => ⟨b,rfl⟩)
    have hClosed : LocallyClosedOriginalPartialTreeCompletable
        Base Base 1 := by
      intro S _ hS
      let e : Structure.Embedding
          (Base.induce (↑S : Set V) hS) Base :=
        Structure.inclusion Base (↑S : Set V) hS
      exact ⟨V, Base, hTree, e,
        e.isEHNHomomorphismEmbedding.toOriginalPartial⟩
    have hLoose : LooseTreeAmalgam Base V Base :=
      LooseTreeAmalgam.copy (Structure.Embedding.id Base)
        (fun b => ⟨b,rfl⟩)
    have hCover : IrreduciblesExtendTo Base Base :=
      hLoose.irreduciblesExtendTo
    exact ⟨V, inferInstance, Base, hKB, hSelf,
      ⟨beta, beta.isEHNHomomorphismEmbedding.toOriginalPartial⟩,
      hClosed, hCover, hLoose⟩

end StructuralRamsey.FunctionalPartite.EHN

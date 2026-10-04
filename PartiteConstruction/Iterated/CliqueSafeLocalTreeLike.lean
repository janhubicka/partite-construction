import PartiteConstruction.Iterated.CliqueExpansion
import PartiteConstruction.Iterated.Initial

/-! # Clique-safe tree witnesses

For the canonical complete-binary expansion we distinguish tree witnesses whose
reduct is still a tree amalgam in the survey's strict sense.

This is stronger than merely being a tree amalgam in the expanded language:
the extra clique relation can make an arbitrary gluing root irreducible
upstairs even when its reduct has no irreducible container.

The paired invariant below keeps both proofs at once.  It is designed for the
actual iterated construction, whose gluing roots arise from controlled copies
of A and hence have natural irreducible containers after reduct.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W X Y H : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}

/-- An expanded tree witness whose clique reduct is also a strict tree
amalgam of copies of the original base. -/
structure CliqueSafeTreeAmalgam
    (B : RelStructure L VB) (T : RelStructure L.withClique W) : Prop where
  expanded : TreeAmalgam B.withClique W T
  reduct : TreeAmalgam B W T.cliqueReduct

namespace CliqueSafeTreeAmalgam

/-- A single canonical expanded copy is clique-safe. -/
theorem copy
    {T : RelStructure L.withClique W}
    (h : Iso B.withClique T) :
    CliqueSafeTreeAmalgam B T := by
  exact ⟨TreeAmalgam.copy h,
    TreeAmalgam.copy h.cliqueReduct⟩

/-- Clique-safe witnesses are closed under a free amalgam whenever the gluing
root has the required irreducible-containment certificates both upstairs and
after clique reduct. -/
theorem glue
    {T₁ : RelStructure L.withClique W}
    {T₂ : RelStructure L.withClique X}
    {D : RelStructure L.withClique H}
    {T : RelStructure L.withClique Y}
    (h₁ : CliqueSafeTreeAmalgam B T₁)
    (h₂ : CliqueSafeTreeAmalgam B T₂)
    (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
    (hc₁ : f₁.ContainedInIrreducible)
    (hc₂ : f₂.ContainedInIrreducible)
    (hc₁r : f₁.cliqueReduct.ContainedInIrreducible)
    (hc₂r : f₂.cliqueReduct.ContainedInIrreducible)
    (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
    (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
    CliqueSafeTreeAmalgam B T := by
  refine ⟨?_, ?_⟩
  · exact TreeAmalgam.glue
      h₁.expanded h₂.expanded f₁ f₂ hc₁ hc₂ i₁ i₂ hfree
  · exact TreeAmalgam.glue
      h₁.reduct h₂.reduct
      f₁.cliqueReduct f₂.cliqueReduct hc₁r hc₂r
      i₁.cliqueReduct i₂.cliqueReduct hfree.cliqueReduct

/-- Forget the safety proof. -/
theorem toTree
    {T : RelStructure L.withClique W}
    (h : CliqueSafeTreeAmalgam B T) :
    TreeAmalgam B.withClique W T :=
  h.expanded

end CliqueSafeTreeAmalgam

/-- Local tree-likeness in the clique expansion, with every chosen target tree
simultaneously certified to remain a strict B-tree after reduct. -/
def CliqueSafeLocallyTreeLike
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C : RelStructure L.withClique W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L.withClique Y),
      CliqueSafeTreeAmalgam B T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A.withClique C,
          ∃ α' : Embedding A.withClique T,
            ∀ a : UA, ∀ ha : α a ∈ S,
              ∃ a' : UA, f ⟨α a, ha⟩ = α' a'

namespace CliqueSafeLocallyTreeLike

/-- A clique-safe witness is an ordinary local-tree witness upstairs. -/
theorem toLocallyTreeLike
    {C : RelStructure L.withClique W} {n : ℕ}
    (h : CliqueSafeLocallyTreeLike A B C n) :
    LocallyTreeLike A.withClique B.withClique C n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, hctrl⟩ := h S hS
  exact ⟨Y, T, hTree.expanded, f, hf, hctrl⟩

/-- Clique-safe local tree-likeness gives strict local tree completability of
the reduct. -/
theorem reduct_locallyTreeCompletable
    {C : RelStructure L.withClique W} {n : ℕ}
    (h : CliqueSafeLocallyTreeLike A B C n) :
    LocallyTreeCompletable B C.cliqueReduct n := by
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
  exact ⟨Y, T.cliqueReduct, hTree.reduct, f, hfr⟩

/-- Monotonicity in the tested size. -/
theorem mono
    {C : RelStructure L.withClique W} {m n : ℕ}
    (h : CliqueSafeLocallyTreeLike A B C n) (hmn : m ≤ n) :
    CliqueSafeLocallyTreeLike A B C m := by
  intro S hS
  exact h S (hS.trans hmn)

end CliqueSafeLocallyTreeLike

namespace PartiteInitial

/-- The disjoint-union initial picture has clique-safe witnesses at every
finite level. -/
theorem cliqueSafe
    {P I : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (β : I → VB ↪ P) [Nonempty I]
    (n : ℕ) :
    CliqueSafeLocallyTreeLike A B
      (Partite.Initial.picture B.withClique β).toRelStructure n := by
  intro S _
  let f : ↥(↑S : Set (I × VB)) → VB := fun x => x.1.2
  have hFold :=
    StructuralRamsey.Partite.Iterated.initial_fold_isHomomorphismEmbedding
      B.withClique β
  have hIncl :
      ((Partite.Initial.picture B.withClique β).toRelStructure.induce
        (↑S : Set (I × VB))).IsHomomorphismEmbedding
        (Partite.Initial.picture B.withClique β).toRelStructure Subtype.val :=
    (inclusion
      (Partite.Initial.picture B.withClique β).toRelStructure
      (↑S : Set (I × VB))).isHomomorphismEmbedding
  have hf :
      ((Partite.Initial.picture B.withClique β).toRelStructure.induce
        (↑S : Set (I × VB))).IsHomomorphismEmbedding B.withClique f := by
    change ((Partite.Initial.picture B.withClique β).toRelStructure.induce
      (↑S : Set (I × VB))).IsHomomorphismEmbedding B.withClique
        (Prod.snd ∘ Subtype.val)
    exact hFold.comp hIncl
  refine ⟨VB, B.withClique,
    CliqueSafeTreeAmalgam.copy (Iso.refl B.withClique), f, hf, ?_⟩
  intro α
  obtain ⟨α', hα'⟩ :=
    hFold.after_irreducible_embedding
      (withClique_hereditarilyIrreducible A).irreducible α
  refine ⟨α', ?_⟩
  intro a ha
  exact ⟨a, (hα' a).symm⟩

end PartiteInitial
end StructuralRamsey.RelStructure

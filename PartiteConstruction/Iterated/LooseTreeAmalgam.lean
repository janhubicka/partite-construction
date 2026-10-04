import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Iterated.TreeCompletion

/-! # Loose tree amalgams

The survey TreeAmalgam definition requires every gluing embedding to have
its image contained in an irreducible substructure on each side. Earlier
definitions used in the EPPA/completion literature allow arbitrary induced
embeddings as gluing roots.

LooseTreeAmalgam removes only those two containment hypotheses. Every survey
tree amalgam is loose, and irreducible substructures still localize to a
constituent base copy because that argument uses only freeness.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- Recursive tree amalgams with unrestricted induced gluing roots. -/
inductive LooseTreeAmalgam (Base : RelStructure L V) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W}
      (h : Iso Base T) : LooseTreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : RelStructure L W₁} {T₂ : RelStructure L W₂}
      {D : RelStructure L Z} {T : RelStructure L W}
      (h₁ : LooseTreeAmalgam Base W₁ T₁)
      (h₂ : LooseTreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      LooseTreeAmalgam Base W T

namespace LooseTreeAmalgam

/-- Every tree amalgam in the stricter survey sense is loose. -/
theorem ofTree
    {Base : RelStructure L V} {T : RelStructure L W}
    (h : TreeAmalgam Base W T) :
    LooseTreeAmalgam Base W T := by
  induction h with
  | copy hIso =>
      exact .copy hIso
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact .glue ih₁ ih₂ f₁ f₂ i₁ i₂ hfree

/-- Irreducible substructures of a loose tree amalgam still lie in a
constituent copy of the base. -/
theorem irreducible_contained_in_copy
    {Base : RelStructure L V} {T : RelStructure L W}
    (hT : LooseTreeAmalgam Base W T)
    {A : RelStructure L U} (hA : A.Irreducible)
    (e : Embedding A T) :
    ∃ j : Embedding Base T, ∀ a : U, ∃ b : V, e a = j b := by
  induction hT with
  | copy h =>
      let j := h.toEmbedding
      refine ⟨j, ?_⟩
      intro a
      refine ⟨h.toEquiv.symm (e a), ?_⟩
      change e a = h.toEquiv (h.toEquiv.symm (e a))
      exact (h.toEquiv.apply_symm_apply (e a)).symm
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ i₁ i₂ hfree ih₁ ih₂ =>
      let S : Set W := Set.range e
      have hS : (T.induce S).Irreducible := hA.range_embedding e
      rcases hfree.irreducible_side S hS with hleft | hright
      · have he : ∀ a : U, ∃ x : W₁, e a = i₁ x := by
          intro a
          exact hleft ⟨e a, ⟨a, rfl⟩⟩
        let e₁ : Embedding A T₁ := e.factorThroughRange i₁ he
        obtain ⟨j₁, hj₁⟩ := ih₁ e₁
        refine ⟨i₁.comp j₁, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₁ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        calc
          e a = i₁ (e₁ a) := hea
          _ = i₁ (j₁ b) := congrArg i₁ hb
      · have he : ∀ a : U, ∃ x : W₂, e a = i₂ x := by
          intro a
          exact hright ⟨e a, ⟨a, rfl⟩⟩
        let e₂ : Embedding A T₂ := e.factorThroughRange i₂ he
        obtain ⟨j₂, hj₂⟩ := ih₂ e₂
        refine ⟨i₂.comp j₂, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₂ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        calc
          e a = i₂ (e₂ a) := hea
          _ = i₂ (j₂ b) := congrArg i₂ hb

/-- Attach one fresh base copy over an arbitrary embedded substructure.
No irreducible-containment certificate is needed. -/
theorem attach
    {Base : RelStructure L V}
    {T : RelStructure L W}
    (hT : LooseTreeAmalgam Base W T)
    {H : Type v} (D : RelStructure L H)
    (eT : Embedding D T) (eB : Embedding D Base) :
    LooseTreeAmalgam Base
      (FreeAmalgam.Vertex D T Base eT eB)
      (FreeAmalgam.amalgam D T Base eT eB) := by
  exact .glue hT (.copy (Iso.refl Base)) eT eB
    (FreeAmalgam.leftEmbedding D T Base eT eB)
    (FreeAmalgam.rightEmbedding D T Base eT eB)
    (FreeAmalgam.isFreeAmalgam D T Base eT eB)

/-- The old target embedding after unrestricted attachment. -/
def attachOldEmbedding
    {Base : RelStructure L V}
    {T : RelStructure L W}
    {H : Type v} (D : RelStructure L H)
    (eT : Embedding D T) (eB : Embedding D Base) :
    Embedding T (FreeAmalgam.amalgam D T Base eT eB) :=
  FreeAmalgam.leftEmbedding D T Base eT eB

/-- The fresh base-copy embedding after unrestricted attachment. -/
def attachFreshEmbedding
    {Base : RelStructure L V}
    {T : RelStructure L W}
    {H : Type v} (D : RelStructure L H)
    (eT : Embedding D T) (eB : Embedding D Base) :
    Embedding Base (FreeAmalgam.amalgam D T Base eT eB) :=
  FreeAmalgam.rightEmbedding D T Base eT eB

end LooseTreeAmalgam

/-- Local tree completability using unrestricted tree amalgams. -/
def LooseLocallyTreeCompletable
    (Base : RelStructure L V) (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L Y),
      LooseTreeAmalgam Base Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f

namespace LocallyTreeCompletable

/-- Restrictive survey tree completability implies loose tree completability. -/
theorem toLoose
    {Base : RelStructure L V} {C : RelStructure L W} {n : ℕ}
    (h : LocallyTreeCompletable Base C n) :
    LooseLocallyTreeCompletable Base C n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf⟩ := h S hS
  exact ⟨Y, T, hTree.ofTree, f, hf⟩

end LocallyTreeCompletable

end StructuralRamsey.RelStructure

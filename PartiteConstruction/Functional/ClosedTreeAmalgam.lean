import PartiteConstruction.Functional.FreeAmalgamClosed
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Function-closed tree amalgams

For graph encodings of set-valued-function structures, an ordinary relational
tree amalgam is too weak: gluing over a non-closed root can create new function
outputs inside a constituent copy.  This file records the strengthening needed
for the functional sparsening construction.

A function-closed tree amalgam has the same strict geometric gluing condition
as the survey's relational `TreeAmalgam`, and in addition requires both root
embeddings at every gluing step to be closed for the distinguished function
graph relations.  The free-amalgam closure calculus then implies that both
side embeddings into the new tree are closed as well.

Consequently constituent copies can be followed through the whole tree by
closed embeddings and therefore decode to full embeddings of function
structures.
-/

namespace StructuralRamsey.RelStructure

open Structure

universe u v
variable {L : Language.{u}}
variable {U V W X Y : Type v}

namespace Iso

/-- A relational isomorphism between graph encodings is automatically closed. -/
def toClosedEmbedding
    {A : RelStructure L.graph V} {B : RelStructure L.graph W}
    (h : Iso A B) :
    ClosedEmbedding A B where
  toEmbedding := h.toEmbedding
  closed := by
    apply (h.toEmbedding.functionClosed_iff_range).2
    intro F x y hy hx
    exact ⟨h.toEquiv.symm y, h.toEquiv.apply_symm_apply y⟩

end Iso

/-- Strict relational tree amalgams with function-closed gluing roots. -/
inductive FunctionClosedTreeAmalgam
    (Base : RelStructure L.graph V) :
    (W : Type v) → RelStructure L.graph W → Prop
  | copy {W : Type v} {T : RelStructure L.graph W}
      (h : Iso Base T) :
      FunctionClosedTreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : RelStructure L.graph W₁}
      {T₂ : RelStructure L.graph W₂}
      {D : RelStructure L.graph Z}
      {T : RelStructure L.graph W}
      (h₁ : FunctionClosedTreeAmalgam Base W₁ T₁)
      (h₂ : FunctionClosedTreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (hf₁ : FunctionClosedMap D T₁ f₁)
      (hf₂ : FunctionClosedMap D T₂ f₂)
      (hc₁ : f₁.ContainedInIrreducible)
      (hc₂ : f₂.ContainedInIrreducible)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      FunctionClosedTreeAmalgam Base W T

namespace FunctionClosedTreeAmalgam

/-- Forgetting closure data gives the ordinary strict relational tree amalgam. -/
theorem toTreeAmalgam
    {Base : RelStructure L.graph V}
    {T : RelStructure L.graph W}
    (hT : FunctionClosedTreeAmalgam Base W T) :
    TreeAmalgam Base W T := by
  induction hT with
  | copy h =>
      exact .copy h
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hf₁ hf₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact .glue ih₁ ih₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree

/-- At a closed-root gluing step, both side embeddings into the amalgam are
closed.  This is exactly the free-amalgam closure observation from Appendix A. -/
theorem glue_sides_closed
    {T₁ : RelStructure L.graph U}
    {T₂ : RelStructure L.graph V}
    {D : RelStructure L.graph W}
    {T : RelStructure L.graph X}
    {f₁ : Embedding D T₁} {f₂ : Embedding D T₂}
    {i₁ : Embedding T₁ T} {i₂ : Embedding T₂ T}
    (hf₁ : FunctionClosedMap D T₁ f₁)
    (hf₂ : FunctionClosedMap D T₂ f₂)
    (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
    FunctionClosedMap T₁ T i₁ ∧ FunctionClosedMap T₂ T i₂ :=
  (hfree.sides_closed_iff).2 ⟨hf₁, hf₂⟩

/-- Every irreducible embedded substructure of a function-closed tree lies in
a constituent copy of the base whose embedding into the whole tree is closed. -/
theorem irreducible_contained_in_closed_copy
    {Base : RelStructure L.graph V} {T : RelStructure L.graph W}
    (hT : FunctionClosedTreeAmalgam Base W T)
    {A : RelStructure L.graph U} (hA : A.Irreducible)
    (e : Embedding A T) :
    ∃ j : ClosedEmbedding Base T,
      ∀ a : U, ∃ b : V, e a = j b := by
  induction hT with
  | copy h =>
      let j := h.toClosedEmbedding
      refine ⟨j, ?_⟩
      intro a
      refine ⟨h.toEquiv.symm (e a), ?_⟩
      change e a = h.toEquiv (h.toEquiv.symm (e a))
      exact (h.toEquiv.apply_symm_apply (e a)).symm
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hf₁ hf₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      let S : Set W := Set.range e
      have hS : (T.induce S).Irreducible := hA.range_embedding e
      have hsides :
          FunctionClosedMap T₁ T i₁ ∧ FunctionClosedMap T₂ T i₂ :=
        glue_sides_closed hf₁ hf₂ hfree
      let ci₁ : ClosedEmbedding T₁ T := {
        toEmbedding := i₁
        closed := hsides.1
      }
      let ci₂ : ClosedEmbedding T₂ T := {
        toEmbedding := i₂
        closed := hsides.2
      }
      rcases hfree.irreducible_side S hS with hleft | hright
      · have he : ∀ a : U, ∃ x : W₁, e a = i₁ x := by
          intro a
          exact hleft ⟨e a, ⟨a, rfl⟩⟩
        let e₁ : Embedding A T₁ := e.factorThroughRange i₁ he
        obtain ⟨j₁, hj₁⟩ := ih₁ e₁
        refine ⟨ClosedEmbedding.comp ci₁ j₁, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₁ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        change e a = i₁ (j₁ b)
        calc
          e a = i₁ (e₁ a) := hea
          _ = i₁ (j₁ b) := congrArg i₁ hb
      · have he : ∀ a : U, ∃ x : W₂, e a = i₂ x := by
          intro a
          exact hright ⟨e a, ⟨a, rfl⟩⟩
        let e₂ : Embedding A T₂ := e.factorThroughRange i₂ he
        obtain ⟨j₂, hj₂⟩ := ih₂ e₂
        refine ⟨ClosedEmbedding.comp ci₂ j₂, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₂ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        change e a = i₂ (j₂ b)
        calc
          e a = i₂ (e₂ a) := hea
          _ = i₂ (j₂ b) := congrArg i₂ hb

/-- In particular, every gluing root satisfying the survey's strict
irreducible-containment condition is contained in a *closed* constituent copy
of the base. -/
theorem root_contained_in_closed_copy
    {Base : RelStructure L.graph V} {T : RelStructure L.graph W}
    (hT : FunctionClosedTreeAmalgam Base W T)
    {D : RelStructure L.graph U}
    (f : Embedding D T) (hf : f.ContainedInIrreducible) :
    ∃ j : ClosedEmbedding Base T,
      ∀ d : U, ∃ b : V, f d = j b := by
  obtain ⟨S, hS, hsub⟩ := hf
  let e : Embedding (T.induce S) T := inclusion T S
  obtain ⟨j, hj⟩ :=
    hT.irreducible_contained_in_closed_copy hS e
  refine ⟨j, ?_⟩
  intro d
  obtain ⟨b, hb⟩ := hj ⟨f d, hsub d⟩
  exact ⟨b, hb⟩

/-- Closed constituent copies decode to full embeddings of the reconstructed
set-valued-function structures. -/
theorem irreducible_contained_in_full_copy
    {Base : RelStructure L.graph V} {T : RelStructure L.graph W}
    (hT : FunctionClosedTreeAmalgam Base W T)
    {A : RelStructure L.graph U} (hA : A.Irreducible)
    (e : Embedding A T) :
    ∃ j : Structure.Embedding (Structure.ofGraph Base) (Structure.ofGraph T),
      ∀ a : U, ∃ b : V, e a = j b := by
  obtain ⟨j, hj⟩ := hT.irreducible_contained_in_closed_copy hA e
  exact ⟨j.toFull, hj⟩

end FunctionClosedTreeAmalgam
end StructuralRamsey.RelStructure

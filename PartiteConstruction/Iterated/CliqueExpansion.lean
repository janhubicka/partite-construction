import PartiteConstruction.Iterated.LooseTreeAmalgam
import PartiteConstruction.Iterated.FinalAttachment
import PartiteConstruction.Ramsey.Basic

/-! # Canonical complete-graph expansion

Add one fresh binary relation interpreted as disequality.  Every injective map
between canonical expansions automatically preserves and reflects the new
relation, so induced embeddings and Ramsey arrows lift functorially.

The expansion makes every induced substructure irreducible.  Forgetting it
from a survey TreeAmalgam yields a LooseTreeAmalgam: freeness survives, while
the extra irreducible-containment certificates need not survive the reduct.
-/
namespace StructuralRamsey

universe u v

/-- Add one fresh binary relation symbol. -/
def RelLanguage.withClique (L : RelLanguage.{u}) : RelLanguage.{u} where
  Symbol := L.Symbol ⊕ Unit
  arity := Sum.elim L.arity (fun _ => 2)

namespace RelStructure

variable {L : RelLanguage.{u}} {V W X Y : Type v}

/-- Canonical expansion by the complete irreflexive binary relation. -/
def withClique (A : RelStructure L V) : RelStructure L.withClique V where
  rel R := by
    cases R with
    | inl R => exact A.rel R
    | inr _ => exact fun (x : Fin 2 → V) => x 0 ≠ x 1

/-- Forget the distinguished complete relation. -/
def cliqueReduct (C : RelStructure L.withClique V) : RelStructure L V where
  rel R := C.rel (.inl R)

@[simp] theorem withClique_reduct (A : RelStructure L V) :
    A.withClique.cliqueReduct = A := rfl

namespace Embedding

/-- Every induced embedding lifts canonically to the complete-graph expansion. -/
def withClique
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    Embedding A.withClique B.withClique where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact e.map_rel_iff R x
    | inr h =>
        cases h
        change e (x (0 : Fin 2)) ≠ e (x (1 : Fin 2)) ↔
          x (0 : Fin 2) ≠ x (1 : Fin 2)
        constructor
        · intro h hxy
          exact h (congrArg e hxy)
        · intro h hxy
          exact h (e.injective hxy)

/-- Forget the complete relation from an induced embedding. -/
def cliqueReduct
    {A : RelStructure L.withClique V} {B : RelStructure L.withClique W}
    (e : Embedding A B) :
    Embedding A.cliqueReduct B.cliqueReduct where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff (.inl R) x

end Embedding

namespace Iso

/-- Forget the complete relation from an isomorphism. -/
def cliqueReduct
    {A : RelStructure L.withClique V} {B : RelStructure L.withClique W}
    (e : Iso A B) :
    Iso A.cliqueReduct B.cliqueReduct where
  toEquiv := e.toEquiv
  map_rel_iff R x := e.map_rel_iff (.inl R) x

end Iso

/-- Every induced substructure of a complete-graph expansion is irreducible. -/
theorem withClique_hereditarilyIrreducible
    (A : RelStructure L V) :
    A.withClique.HereditarilyIrreducible := by
  intro S x y hxy
  have hval : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  let q : Fin 2 → S := ![x, y]
  refine ⟨(.inr () : L.withClique.Symbol), q,
    (0 : Fin 2), (1 : Fin 2), ?_, rfl, rfl⟩
  change x.1 ≠ y.1
  exact hval

/-- Irreducibility in the reduct implies irreducibility of the corresponding
induced expanded substructure. -/
theorem irreducible_withClique_of_reduct
    (C : RelStructure L.withClique V) (S : Set V)
    (hS : (C.cliqueReduct.induce S).Irreducible) :
    (C.induce S).Irreducible := by
  intro x y hxy
  obtain ⟨R, q, i, j, hq, hqi, hqj⟩ := hS hxy
  refine ⟨(.inl R : L.withClique.Symbol), q, i, j, ?_, hqi, hqj⟩
  exact hq

namespace IsHomomorphismEmbedding

/-- Forgetting the complete relation preserves homomorphism-embeddings. -/
theorem cliqueReduct
    {A : RelStructure L.withClique V} {B : RelStructure L.withClique W}
    {f : V → W}
    (h : A.IsHomomorphismEmbedding B f) :
    A.cliqueReduct.IsHomomorphismEmbedding B.cliqueReduct f := by
  constructor
  · intro R x hx
    exact h.1 (.inl R) x hx
  · intro S hS
    have hSplus : (A.induce S).Irreducible :=
      irreducible_withClique_of_reduct A S hS
    obtain ⟨e, he⟩ := h.embeddingOn S hSplus
    let er : Embedding (A.cliqueReduct.induce S) B.cliqueReduct := {
      toFun := e
      injective := e.injective
      map_rel_iff := fun R x => e.map_rel_iff (.inl R) x
    }
    exact ⟨er, he⟩

end IsHomomorphismEmbedding

namespace IsFreeAmalgam

/-- Forgetting the complete relation preserves the concrete free-amalgam
diagram. -/
theorem cliqueReduct
    {D : RelStructure L.withClique V}
    {A : RelStructure L.withClique W}
    {B : RelStructure L.withClique X}
    {C : RelStructure L.withClique Y}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (h : IsFreeAmalgam fA fB iA iB) :
    IsFreeAmalgam fA.cliqueReduct fB.cliqueReduct
      iA.cliqueReduct iB.cliqueReduct := by
  refine ⟨h.covers, h.overlap, ?_⟩
  intro R q
  exact h.rel_iff (.inl R) q

end IsFreeAmalgam

namespace TreeAmalgam

/-- Forgetting the complete relation turns a survey tree amalgam into a loose
tree amalgam of the reducts. -/
theorem cliqueReduct_loose
    {Base : RelStructure L.withClique V}
    {T : RelStructure L.withClique W}
    (hT : TreeAmalgam Base W T) :
    LooseTreeAmalgam Base.cliqueReduct W T.cliqueReduct := by
  induction hT with
  | copy h =>
      exact .copy h.cliqueReduct
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact .glue ih₁ ih₂
        f₁.cliqueReduct f₂.cliqueReduct
        i₁.cliqueReduct i₂.cliqueReduct
        hfree.cliqueReduct

end TreeAmalgam

/-- Forgetting the complete relation from local tree-likeness leaves the
completion property with loose tree amalgams. -/
theorem LocallyTreeLike.cliqueReduct_loose
    {A : RelStructure L.withClique V}
    {B : RelStructure L.withClique W}
    {C : RelStructure L.withClique X}
    {n : ℕ}
    (h : LocallyTreeLike A B C n) :
    LooseLocallyTreeCompletable B.cliqueReduct C.cliqueReduct n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, _⟩ := h S hS
  have hfr :
      (C.cliqueReduct.induce (↑S : Set X)).IsHomomorphismEmbedding
        T.cliqueReduct f := by
    simpa [cliqueReduct] using hf.cliqueReduct
  exact ⟨Y, T.cliqueReduct, hTree.cliqueReduct_loose, f, hfr⟩

/-- Property (3) descends through the complete-relation reduct. -/
theorem IrreduciblesExtendTo.cliqueReduct
    {B : RelStructure L.withClique V}
    {C : RelStructure L.withClique W}
    (h : IrreduciblesExtendTo B C) :
    IrreduciblesExtendTo B.cliqueReduct C.cliqueReduct := by
  intro S hS
  have hSplus : (C.induce S).Irreducible :=
    irreducible_withClique_of_reduct C S hS
  obtain ⟨e, he⟩ := h S hSplus
  exact ⟨e.cliqueReduct, he⟩

end RelStructure

/-- Ramsey arrows lift to the canonical complete-graph expansion. -/
theorem arrow_withClique
    {L : RelLanguage.{u}}
    {U V W : Type v}
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (κ : Type*)
    (h : Arrow A B C κ) :
    Arrow A.withClique B.withClique C.withClique κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ e.withClique)
  refine ⟨f.withClique, ?_⟩
  intro e₁ e₂
  have hh := hf e₁.cliqueReduct e₂.cliqueReduct
  have he₁ :
      (f.comp e₁.cliqueReduct).withClique =
        f.withClique.comp e₁ := by
    apply RelStructure.Embedding.ext
    intro a
    rfl
  have he₂ :
      (f.comp e₂.cliqueReduct).withClique =
        f.withClique.comp e₂ := by
    apply RelStructure.Embedding.ext
    intro a
    rfl
  rw [← he₁, ← he₂]
  exact hh

/-- Forgetting the complete relation from a Ramsey witness preserves the arrow
for the canonical source and target expansions. -/
theorem arrow_cliqueReduct
    {L : RelLanguage.{u}}
    {U V W : Type v}
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L.withClique W) (κ : Type*)
    (h : Arrow A.withClique B.withClique C κ) :
    Arrow A B C.cliqueReduct κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ e.cliqueReduct)
  refine ⟨f.cliqueReduct, ?_⟩
  intro e₁ e₂
  have hh := hf e₁.withClique e₂.withClique
  have he₁ :
      (f.comp e₁.withClique).cliqueReduct =
        f.cliqueReduct.comp e₁ := by
    apply RelStructure.Embedding.ext
    intro a
    rfl
  have he₂ :
      (f.comp e₂.withClique).cliqueReduct =
        f.cliqueReduct.comp e₂ := by
    apply RelStructure.Embedding.ext
    intro a
    rfl
  rw [← he₁, ← he₂]
  exact hh

end StructuralRamsey

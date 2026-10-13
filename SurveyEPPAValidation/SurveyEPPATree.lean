import SurveyEPPAForbiddenNullary

/-!
# The survey's tree-amalgam notion versus the EPPA paper's

The survey's Definition `defn:tree-amalgamation` allows gluing over any
interface whose image in each existing side is contained in an
irreducible substructure of that side. The EPPA paper's actual full-A
tree-amalgam constructor insists that the interface lie in a named
copy of the original A on *both* sides.

For irreducible A, the paper's constructor therefore implies the
survey's condition. This file checks the implication on actual
amalgamated structures (not merely on an abstract incidence tree),
and upgrades the restricted EPPA theorem to a survey-facing statement
with the weaker survey tree-amalgam predicate and the survey's exact
unary-function homomorphism-embedding semantics.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- Literal recursive tree amalgams from the survey: in every gluing step,
the overlap image on each side is contained in an irreducible embedded
substructure. This is weaker than requiring the overlap to lie in a
distinguished copy of A; the underlying free gluing is the concrete
`TreeLike.generalAmalgamStructure` from the verified EPPA library. -/
inductive SurveyTreeAmalgamation
    {U : Type (max u v)}
    (act : L.Action Γ) (A : Structure L U) :
    {V : Type (max u v)} → Structure L V → Prop where
  | copy {V : Type (max u v)}
      (H : Structure L V)
      (e : Structure.Embedding act A H)
      (onto : Function.Surjective e.toFun) :
      SurveyTreeAmalgamation act A H
  | glue {I X Y : Type (max u v)}
      (C : Structure L I)
      (B₁ : Structure L X) (B₂ : Structure L Y)
      (h₁ : SurveyTreeAmalgamation act A B₁)
      (h₂ : SurveyTreeAmalgamation act A B₂)
      (f : Structure.Embedding act C B₁)
      (g : Structure.Embedding act C B₂)
      (hLeft :
        ∃ (J : Type (max u v)) (D : Structure L J),
          D.IsIrreducible ∧
            ∃ j : Structure.Embedding act D B₁,
              Set.range f.toFun ⊆ Set.range j.toFun)
      (hRight :
        ∃ (J : Type (max u v)) (D : Structure L J),
          D.IsIrreducible ∧
            ∃ j : Structure.Embedding act D B₂,
              Set.range g.toFun ⊆ Set.range j.toFun) :
      SurveyTreeAmalgamation act A
        (TreeLike.generalAmalgamStructure act f g)

/-- The EPPA paper's stronger full-A-copy tree notion implies the
literal survey tree-amalgam notion whenever A is irreducible.
Every gluing image is already contained in the displayed A-copy. -/
theorem fullCopyTree_isSurveyTree
    {U : Type (max u v)}
    (act : L.Action Γ)
    (A : Structure L U)
    (hIrr : A.IsIrreducible)
    {V : Type (max u v)} {H : Structure L V}
    (hTree : TreeLike.TreeAmalgamation act A H) :
    SurveyTreeAmalgamation act A H := by
  induction hTree with
  | copy C e hSurj =>
      exact SurveyTreeAmalgamation.copy C e hSurj
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      refine SurveyTreeAmalgamation.glue
        C B₁ B₂ ih₁ ih₂
        (α₁.comp δ₁) (α₂.comp δ₂) ?_ ?_
      · refine ⟨U, A, hIrr, α₁, ?_⟩
        rintro y ⟨x, hx⟩
        exact ⟨δ₁ x, hx⟩
      · refine ⟨U, A, hIrr, α₂, ?_⟩
        rintro y ⟨x, hx⟩
        exact ⟨δ₂ x, hx⟩

/-- The restricted theorem `thm:hkn` with **both** differences
from the EPPA paper's conventions resolved: exact function images
for unary homomorphism-embeddings, and the survey's more permissive
tree-amalgam definition. -/
theorem restrictedEPPA_withSurveyTreeAmalgam
    {α β : Type (max u v)} [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : Structure L α)
    (hIrr : A.IsIrreducible)
    (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : Structure L δ) (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      (∃ f : Structure.Homomorphism act B B₀,
        IsSurveyHomomorphismEmbedding act f) ∧
      (∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            SurveyTreeAmalgamation act A H ∧
            ∃ f : Structure.Homomorphism act (B.induce S hS) H,
              IsSurveyHomomorphismEmbedding act f) ∧
      (Structure.IsCoherentEPPAWitness act ψ →
        Structure.IsCoherentEPPAWitness act ι) := by
  obtain ⟨δ, hδ, B, ι, hEPPAnew, hFaith, hProjection,
      hTrees, hCoherentTransfer⟩ :=
    restrictedEPPA_withSurveyFunctionSemantics
      act A B₀ ψ hEPPA n
  refine ⟨δ, hδ, B, ι, hEPPAnew, hFaith,
    hProjection, ?_, hCoherentTransfer⟩
  intro S hS hBound
  obtain ⟨W, H, hTree, f, hf⟩ := hTrees S hS hBound
  exact ⟨W, H, fullCopyTree_isSurveyTree act A hIrr hTree,
    f, hf⟩

/-- Full fixed-nullary version of the survey's restricted theorem:
the added nullary truth values remain unchanged, and local trees
satisfy the survey's gluing convention. -/
theorem restrictedEPPA_withFixedNullaries_andSurveyTree
    {Z : Type x}
    {α β : Type (max u v)} [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : WithFixedNullaryRelations L Z α)
    (hIrr : A.positive.IsIrreducible)
    (B₀ : WithFixedNullaryRelations L Z β)
    (ψ : FixedNullaryEmbedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ.positive)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : WithFixedNullaryRelations L Z δ)
      (ι : FixedNullaryEmbedding act A B),
        Structure.IsEPPAWitness act ι.positive ∧
        Structure.IsIrreducibleStructureFaithful act ι.positive ∧
        (∃ f : Structure.Homomorphism act B.positive B₀.positive,
          IsSurveyHomomorphismEmbedding act f) ∧
        (∀ (S : Set δ) (hS : B.positive.IsClosed S),
          S.ncard ≤ n →
            ∃ (W : Type (max u v)) (H : Structure L W),
              SurveyTreeAmalgamation act A.positive H ∧
              ∃ f : Structure.Homomorphism act
                  (B.positive.induce S hS) H,
                IsSurveyHomomorphismEmbedding act f) ∧
        (Structure.IsCoherentEPPAWitness act ψ.positive →
          Structure.IsCoherentEPPAWitness act ι.positive) := by
  obtain ⟨δ, hδ, B, ι, hEPPAnew, hFaith, hProjection,
      hTrees, hCoherentTransfer⟩ :=
    restrictedEPPA_withFixedNullaryRelations
      act A B₀ ψ hEPPA n
  refine ⟨δ, hδ, B, ι, hEPPAnew, hFaith,
    hProjection, ?_, hCoherentTransfer⟩
  intro S hS hBound
  obtain ⟨W, H, hTree, f, hf⟩ := hTrees S hS hBound
  exact ⟨W, H, fullCopyTree_isSurveyTree
    act A.positive hIrr hTree, f, hf⟩

end SurveyEPPA

import SurveyEPPA

/-!
# Nullary relations in the survey's ordinary-language presentation

AllThoseEPPA.Language represents relation symbols of strictly positive
arity. An arbitrary set Z of nullary relation symbols can be split off:
an interpretation of each zero-ary relation is simply a truth value,
independent of the vertices. Under the survey's identity-only language
action, these values are necessarily fixed by every embedding and
automorphism, and are the same in every substructure.

We formalize that split presentation as `WithFixedNullaryRelations`
and lift the verified unrestricted and restricted EPPA witnesses without
ever discarding the nullary truth assignments. The construction also
works with arbitrary Γ-actions on the POSITIVE-arity symbols provided
the nullary symbols themselves are fixed.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- Exactly a positive-arity Γ-structure together with an interpretation
of arbitrarily many fixed nullary relation symbols. -/
structure WithFixedNullaryRelations
    (L : Language.{u}) (Z : Type x) (V : Type (max u v)) where
  positive : Structure L V
  nullary : Z → Prop

/-- Exact embedding in the split presentation, including all nullary
relations. Their interpretations agree in domain and codomain. -/
structure FixedNullaryEmbedding
    (act : L.Action Γ)
    {V W : Type (max u v)}
    (A : WithFixedNullaryRelations L Z V)
    (B : WithFixedNullaryRelations L Z W) where
  positive : Structure.Embedding act A.positive B.positive
  nullary_eq : A.nullary = B.nullary

/-- All partial automorphisms of the positive reduct preserve the fixed
nullary interpretations automatically. Thus this is the actual type of
partial automorphisms of the split structure. -/
abbrev FixedNullaryPartialAutomorphism
    (act : L.Action Γ)
    {V : Type (max u v)}
    (A : WithFixedNullaryRelations L Z V) :=
  Structure.PartialAutomorphism act A.positive

/-- Coherent EPPA in the split presentation; the positive automorphisms
also preserve every fixed nullary relation, since the nullary functions
are literally identical in A and B. -/
def IsCoherentFixedNullaryEPPAWitness
    (act : L.Action Γ)
    {V W : Type (max u v)}
    {A : WithFixedNullaryRelations L Z V}
    {B : WithFixedNullaryRelations L Z W}
    (ι : FixedNullaryEmbedding act A B) : Prop :=
  Structure.IsCoherentEPPAWitness act ι.positive

/-- A genuine faithful coherent finite EPPA witness when the language
also has arbitrary fixed nullary relations. -/
theorem unrestrictedEPPA_withFixedNullaryRelations
    (act : L.Action Γ)
    {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α)
    (hOrbit : A.positive.HasFiniteRelabelOrbit act) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : WithFixedNullaryRelations L Z β)
      (ι : FixedNullaryEmbedding act A B),
        IsCoherentFixedNullaryEPPAWitness act ι ∧
        Structure.IsIrreducibleStructureFaithful act ι.positive := by
  obtain ⟨β, hβ, B, e, hCoherent, hFaithful⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA act A.positive hOrbit
  exact ⟨β, hβ, ⟨B, A.nullary⟩, ⟨e, rfl⟩, hCoherent, hFaithful⟩

/-- Ordinary languages (trivial symbol action) have the finite relabelling
orbit hypothesis automatically, including an infinite set of nullary
relation symbols. -/
theorem unrestrictedEPPA_withNullaries_trivialAction
    [Finite Γ]
    {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : WithFixedNullaryRelations L Z β)
      (ι : FixedNullaryEmbedding (Language.Action.trivial L Γ) A B),
        IsCoherentFixedNullaryEPPAWitness
          (Language.Action.trivial L Γ) ι ∧
        Structure.IsIrreducibleStructureFaithful
          (Language.Action.trivial L Γ) ι.positive := by
  have hOrbit : A.positive.HasFiniteRelabelOrbit
      (Language.Action.trivial L Γ) := by
    unfold Structure.HasFiniteRelabelOrbit
    exact Set.finite_range _
  exact unrestrictedEPPA_withFixedNullaryRelations
    (Language.Action.trivial L Γ) A hOrbit

/-- Restricted EPPA also transports all fixed nullary relations. The
locally tree-like conclusion is on the positive reduct, and every full
copy used by the tree receives the same nullary interpretation as A. -/
theorem restrictedEPPA_withFixedNullaryRelations
    {α β : Type (max u v)} [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : WithFixedNullaryRelations L Z α)
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
              TreeLike.TreeAmalgamation act A.positive H ∧
              ∃ f : Structure.Homomorphism act
                  (B.positive.induce S hS) H,
                IsSurveyHomomorphismEmbedding act f) ∧
        (Structure.IsCoherentEPPAWitness act ψ.positive →
          Structure.IsCoherentEPPAWitness act ι.positive) := by
  obtain ⟨δ, hδ, B, e, hEPPAnew, hFaithful, hProjection,
      hTrees, hCoherence⟩ :=
    restrictedEPPA_withSurveyFunctionSemantics
      act A.positive B₀.positive ψ.positive hEPPA n
  exact ⟨δ, hδ, ⟨B, A.nullary⟩, ⟨e, rfl⟩,
    hEPPAnew, hFaithful, hProjection, hTrees, hCoherence⟩

end SurveyEPPA

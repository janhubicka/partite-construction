import SurveyEPPANullary

/-!
# Locally finite EPPA transfer for classes with nullary relations

The survey permits arbitrary nullary relation symbols, while the reusable
AllThoseEPPA language has only positive-arity relation symbols. Nullary
symbols interpreted in an ordinary (non-language-permuting) structure form
a truth-value profile `ν : Z → Prop`.

Embeddings can only occur within one nullary profile. Thus hereditary strong
amalgamation classes of structures in the full language decompose into
classes indexed by profiles, and the general locally finite EPPA transfer
can be applied separately in each profile. This file expresses that
decomposition explicitly instead of assuming that the ambient class or its
forbidden configurations are independent of the nullary relations.

The local-finiteness hypothesis used below remains the SURVEY'S requirement:
every irreducible of a test structure extends to an internal full A-copy.
Theorem `locallyFiniteEPPA_surveyCriterion` already verified this
stronger-structured input as the correct bridge to the original EPPA paper.

In the full language, the profile is unchanged by all embeddings and partial
automorphisms; hence positive-part automorphisms lift automatically to the
split structure with the same profile.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- A class of arbitrary split-language structures is represented by one
hereditary, strong-amalgamation positive-language class for each possible
interpretation of the nullary symbols. This is not a single common slice:
the membership conditions may vary freely with the profile ν. -/
abbrev NullarySlicedHereditaryStrongAmalgamationClass
    (act : L.Action Γ) (Z : Type x) :=
  (ν : Z → Prop) → TreeLike.HereditaryFiniteStrongAmalgamationClass act

/-- A fixed-nullary-language class has ordinary EPPA: every finite member
has an EPPA-witness of the SAME nullary profile in the class. -/
def FixedNullaryClassHasEPPA
    (act : L.Action Γ)
    (K : NullarySlicedHereditaryStrongAmalgamationClass act Z) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α),
    (K A.nullary).toAmalgamationClass.mem A.positive →
      ∃ (β : Type (max u v)) (_ : Finite β)
        (B : WithFixedNullaryRelations L Z β)
        (ι : FixedNullaryEmbedding act A B),
        (K B.nullary).toAmalgamationClass.mem B.positive ∧
        Structure.IsEPPAWitness act ι.positive

/-- Coherent version, including faithful extension of each partial
automorphism of the original split structure. -/
def FixedNullaryClassHasCoherentEPPA
    (act : L.Action Γ)
    (K : NullarySlicedHereditaryStrongAmalgamationClass act Z) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α),
    (K A.nullary).toAmalgamationClass.mem A.positive →
      ∃ (β : Type (max u v)) (_ : Finite β)
        (B : WithFixedNullaryRelations L Z β)
        (ι : FixedNullaryEmbedding act A B),
        (K B.nullary).toAmalgamationClass.mem B.positive ∧
        IsCoherentFixedNullaryEPPAWitness act ι

/-- The *full* class-level EPPA theorem in the survey's split language,
including arbitrary fixed nullary relations and its actual internally
extendible local-finiteness condition.

The assumptions are made separately in each nullary profile, exactly as
required for classes whose membership depends on the nullary symbols. -/
theorem locallyFiniteEPPA_withFixedNullaryRelations
    (act : L.Action Γ)
    (K : NullarySlicedHereditaryStrongAmalgamationClass act Z)
    (E : (ν : Z → Prop) →
      {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (K ν).toAmalgamationClass.mem A → E ν A)
    (hE :
      ∀ ν : Z → Prop, TreeLike.FiniteClassHasEPPA act (E ν))
    (hIrr :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (K ν).toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocal :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        (K ν).toAmalgamationClass.mem A → E ν B₀ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (K ν).toAmalgamationClass) :
    FixedNullaryClassHasEPPA act K := by
  intro α hα A hKA
  obtain ⟨β, hβ, B, ι, hKB, hEPPA⟩ :=
    (locallyFiniteEPPA_surveyCriterion
      act (K A.nullary) (E A.nullary)
      (hSub A.nullary) (hE A.nullary)
      (hIrr A.nullary) (hLocal A.nullary))
      A.positive hKA
  exact ⟨β, hβ,
    ⟨B, A.nullary⟩, ⟨ι, rfl⟩, hKB, hEPPA⟩

/-- The coherent locally finite EPPA transfer in the entire split language.
The ordinary small-completion hypotheses are unchanged. No coherent
completion is required: the automorphism-preserving group-homomorphic lift
transports the coherent choice of partial-automorphism extensions. -/
theorem locallyFiniteCoherentEPPA_withFixedNullaryRelations
    (act : L.Action Γ)
    (K : NullarySlicedHereditaryStrongAmalgamationClass act Z)
    (E : (ν : Z → Prop) →
      {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (K ν).toAmalgamationClass.mem A → E ν A)
    (hE :
      ∀ ν : Z → Prop, TreeLike.FiniteClassHasCoherentEPPA act (E ν))
    (hIrr :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (K ν).toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocal :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        (K ν).toAmalgamationClass.mem A → E ν B₀ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (K ν).toAmalgamationClass) :
    FixedNullaryClassHasCoherentEPPA act K := by
  intro α hα A hKA
  obtain ⟨β, hβ, B, ι, hKB, hCoherent⟩ :=
    (locallyFiniteCoherentEPPA_surveyCriterion
      act (K A.nullary) (E A.nullary)
      (hSub A.nullary) (hE A.nullary)
      (hIrr A.nullary) (hLocal A.nullary))
      A.positive hKA
  exact ⟨β, hβ,
    ⟨B, A.nullary⟩, ⟨ι, rfl⟩, hKB, hCoherent⟩

end SurveyEPPA

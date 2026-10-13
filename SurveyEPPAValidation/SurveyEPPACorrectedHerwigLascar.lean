import SurveyEPPADirectClasses

/-!
# Corrected generalized Herwig--Lascar theorem in the survey language

The survey's displayed unconditional finite-forbidden-HOMOMORPHISM theorem
is false (the directed path length two gives a counterexample). The
checked AllThoseEPPA theorem is conditional:

* the forbidden family is finite and exclusion means no
  HOMOMORPHISM-EMBEDDING of a forbidden structure;
* the finite source embeds in a possibly infinite forbidden-free
  ambient structure that extends all source partial automorphisms;
* the source has finite orbit under the Γ relabelling action.

This file transports this exact valid statement to the survey's
full fixed-language convention with arbitrary fixed nullary symbols.
Forbiddance can depend on the entire nullary truth-value profile.
No replacement of the ambient hypothesis or the morphism convention
is made. A second theorem specializes to ordinary fixed languages.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- Valid generalized Herwig--Lascar theorem with fixed nullary
relations. The ambient model may be infinite, but its nullary
truth-value profile must agree with the source, as enforced by the
full-language embedding. -/
theorem generalizedHerwigLascar_withFixedNullaries
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    {α : Type (max u v)} [Finite α]
    {M : Type (max u v)}
    (A : WithFixedNullaryRelations L Z α)
    (hOrbit : A.positive.HasFiniteRelabelOrbit act)
    (N : WithFixedNullaryRelations L Z M)
    (a : FixedNullaryEmbedding act A N)
    (hAmbientEPPA : Structure.IsEPPAWitness act a.positive)
    (hAmbientAvoids : (F N.nullary).Avoids act N.positive) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : WithFixedNullaryRelations L Z δ)
      (ι : FixedNullaryEmbedding act A B),
        IsCoherentFixedNullaryEPPAWitness act ι ∧
        Structure.IsIrreducibleStructureFaithful act ι.positive ∧
        (F B.nullary).Avoids act B.positive := by
  have hAvoidAtSource :
      (F A.nullary).Avoids act N.positive := by
    rw [a.nullary_eq]
    exact hAmbientAvoids
  obtain ⟨δ, hδ, B, ι, hCoherent, hFaith, hAvoid⟩ :=
    MainTheorems.herwigLascar
      (F A.nullary) act A.positive hOrbit
      N.positive a.positive hAmbientEPPA hAvoidAtSource
  exact ⟨δ, hδ, ⟨B, A.nullary⟩, ⟨ι, rfl⟩,
    hCoherent, hFaith, hAvoid⟩

/-- Ordinary (non-permuting) language symbols admit the corrected
theorem without a separate orbit hypothesis: every finite Γ
satisfies it, including the trivial one-element group. This does
NOT remove the essential ambient-extension assumption. -/
theorem generalizedHerwigLascar_withFixedNullaries_trivialAction
    [Finite Γ]
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    {α : Type (max u v)} [Finite α]
    {M : Type (max u v)}
    (A : WithFixedNullaryRelations L Z α)
    (N : WithFixedNullaryRelations L Z M)
    (a : FixedNullaryEmbedding (Language.Action.trivial L Γ) A N)
    (hAmbientEPPA : Structure.IsEPPAWitness
      (Language.Action.trivial L Γ) a.positive)
    (hAmbientAvoids : (F N.nullary).Avoids
      (Language.Action.trivial L Γ) N.positive) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : WithFixedNullaryRelations L Z δ)
      (ι : FixedNullaryEmbedding (Language.Action.trivial L Γ) A B),
        IsCoherentFixedNullaryEPPAWitness
          (Language.Action.trivial L Γ) ι ∧
        Structure.IsIrreducibleStructureFaithful
          (Language.Action.trivial L Γ) ι.positive ∧
        (F B.nullary).Avoids
          (Language.Action.trivial L Γ) B.positive := by
  have hOrbit : A.positive.HasFiniteRelabelOrbit
      (Language.Action.trivial L Γ) := by
    unfold Structure.HasFiniteRelabelOrbit
    exact Set.finite_range _
  exact generalizedHerwigLascar_withFixedNullaries
    F (Language.Action.trivial L Γ) A hOrbit N
    a hAmbientEPPA hAmbientAvoids

end SurveyEPPA

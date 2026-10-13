import SurveyEPPAForbidden

/-!
# Forbidden irreducibles in the full survey language (including nullaries)

A language with nullary relation symbols is represented as a positive-arity
EPPA structure plus a truth-value profile `ν : Z → Prop`. Every embedding
preserves ν, but an irreducible forbidden family may depend on ν.

This file packages a possibly different finite family of irreducible
patterns for each nullary profile and proves coherent EPPA of the entire
forbidden class. No assumption that class membership ignores nullary
relations is imposed.

It is a direct corollary of the faithful coherent EPPA theorem and the
previously formalized exact-fibre/nullary semantics, not an application
of the false unconditional forbidden-homomorphism statement identified
in the survey.
-/

namespace SurveyEPPA
namespace IrreducibleForb

open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- A possibly different finite family of forbidden irreducible structures
for every interpretation of all fixed nullary relation symbols. -/
def AvoidsEmbeddingsWithNullaries
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    {α : Type (max u v)}
    (A : WithFixedNullaryRelations L Z α) : Prop :=
  AvoidsEmbeddings (F A.nullary) act A.positive

/-- The paper's prohibition of homomorphism-embeddings coincides with
the survey's prohibition of embeddings for irreducible forbidden models,
within each nullary truth-value profile. -/
theorem avoidsEmbeddingsWithNullaries_iff_homEmbeddingAvoidance
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible :
      ∀ (ν : Z → Prop) (i : (F ν).Code),
        ((F ν).model i).IsIrreducible)
    {α : Type (max u v)}
    (A : WithFixedNullaryRelations L Z α) :
    AvoidsEmbeddingsWithNullaries F act A ↔
      (F A.nullary).Avoids act A.positive := by
  exact avoidsEmbeddings_iff_avoidsHomomorphismEmbeddings
    (F A.nullary) act (hIrreducible A.nullary) A.positive

/-- The survey's faithful unrestricted coherent EPPA theorem yields
coherent EPPA for any class forbidding irreducibles, even if which
patterns are forbidden depends on the nullary interpretation. -/
theorem irreducibleForbiddenClass_withNullaries_hasCoherentEPPA
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible :
      ∀ (ν : Z → Prop) (i : (F ν).Code),
        ((F ν).model i).IsIrreducible)
    (hOrbit :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        AvoidsEmbeddingsWithNullaries F act A →
          A.positive.HasFiniteRelabelOrbit act) :
    FullFixedNullaryClassHasCoherentEPPA act
      (fun {α : Type (max u v)}
        (A : WithFixedNullaryRelations L Z α) =>
          AvoidsEmbeddingsWithNullaries F act A) := by
  intro α hα A hAvoid
  obtain ⟨β, hβ, B, ι, hAvoidB, hCoherent, _hFaith⟩ :=
    faithfulCoherentEPPA_preserves_irreducible_forbidden
      (F A.nullary) act (hIrreducible A.nullary)
      A.positive (hOrbit A hAvoid) hAvoid
  exact ⟨β, hβ, ⟨B, A.nullary⟩, ⟨ι, rfl⟩,
    hAvoidB, hCoherent⟩

/-- For the ordinary-language interpretation of the survey, choose a
finite group acting trivially on all symbols, in particular the
one-element group. Thus no finite-orbit assumption is needed on
individual A and every finite irreducible-forbidden full-language
class (with arbitrary fixed nullaries) has coherent EPPA. -/
theorem irreducibleForbiddenClass_withNullaries_hasCoherentEPPA_trivialAction
    [Finite Γ]
    (F : (ν : Z → Prop) →
      HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (hIrreducible :
      ∀ (ν : Z → Prop) (i : (F ν).Code),
        ((F ν).model i).IsIrreducible) :
    FullFixedNullaryClassHasCoherentEPPA
      (Language.Action.trivial L Γ)
      (fun {α : Type (max u v)}
        (A : WithFixedNullaryRelations L Z α) =>
          AvoidsEmbeddingsWithNullaries F
            (Language.Action.trivial L Γ) A) := by
  apply irreducibleForbiddenClass_withNullaries_hasCoherentEPPA
    F (Language.Action.trivial L Γ) hIrreducible
  intro α hα A hAvoid
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

end IrreducibleForb
end SurveyEPPA

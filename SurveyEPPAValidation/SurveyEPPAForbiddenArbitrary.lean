import SurveyEPPATree

/-!
# Coherent EPPA for arbitrary (possibly infinite) irreducible-forbidden families

The faithful EPPA construction does not need the forbidden family itself
to be finite. Each forbidden structure may also have its own carrier type.
The key is that *every* forbidden pattern is irreducible and forbiddenness
is defined by the survey's embeddings, not arbitrary homomorphisms.

We do not reuse the generalized Herwig–Lascar finite-family interface for
this result; the faithful-to-cuts bridge proves the stronger arbitrary-
family corollary directly. This also applies in a full language with
fixed nullary relations when the forbidden family may vary by profile.
-/

namespace SurveyEPPA
namespace IrreducibleForb

open AllThoseEPPA

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- An arbitrary indexed family of irreducible structures, potentially
infinitely many and with heterogeneous (possibly infinite) carriers.
No finiteness of the family, its code type, or its carriers is assumed. -/
structure ArbitraryIrreducibleFamily (L : Language.{u}) where
  Code : Type v
  Carrier : Code → Type (max u v)
  model : (i : Code) → Structure L (Carrier i)
  irreducible : ∀ i : Code, (model i).IsIrreducible

/-- Absence of all embeddings of forbidden irreducible patterns. -/
def AvoidsArbitraryIrreducibles
    (F : ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    {β : Type (max u v)} (B : Structure L β) : Prop :=
  ∀ i : F.Code,
    ¬ Nonempty (Structure.Embedding act (F.model i) B)

/-- Faithfulness forbids any indexed family of irreducibles, not just
a finite family and not just a single irreducible. -/
theorem faithful_preserves_arbitrary_irreducible_family
    (F : ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    {α β : Type (max u v)}
    (A : Structure L α) (B : Structure L β)
    (ι : Structure.Embedding act A B)
    (hFaith : Structure.IsIrreducibleStructureFaithful act ι)
    (hAvoid : AvoidsArbitraryIrreducibles F act A) :
    AvoidsArbitraryIrreducibles F act B := by
  have hEvery : TreeLike.EveryIrreducibleEmbedsIn act A B :=
    TreeLike.everyIrreducibleEmbedsIn_of_faithful act A B ι hFaith
  intro i hBad
  obtain ⟨e⟩ := hBad
  obtain ⟨j⟩ := hEvery
    (Set.range e.toFun) (e.range_isClosed act)
    (e.range_isIrreducible act (F.irreducible i))
  exact hAvoid i ⟨j.comp (e.toClosedRange act)⟩

/-- Unrestricted faithful coherent EPPA preserves every member of
an arbitrary forbidden irreducible family, provided the given finite
source has finite symbol-relabel orbit. -/
theorem arbitraryIrreducibleFree_faithfulCoherentEPPA
    (F : ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    {α : Type (max u v)} [Finite α]
    (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act)
    (hAvoid : AvoidsArbitraryIrreducibles F act A) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : Structure L β) (ι : Structure.Embedding act A B),
      AvoidsArbitraryIrreducibles F act B ∧
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  obtain ⟨β, hβ, B, ι, hCoherent, hFaith⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA act A hOrbit
  exact ⟨β, hβ, B, ι,
    faithful_preserves_arbitrary_irreducible_family
      F act A B ι hFaith hAvoid,
    hCoherent, hFaith⟩

/-- Every class defined by an arbitrary irreducible-forbidden family
has coherent EPPA under the necessary finite-orbit condition. -/
theorem arbitraryIrreducibleForbiddenClass_hasCoherentEPPA
    (F : ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    (hOrbit :
      ∀ {α : Type (max u v)} [Finite α] (A : Structure L α),
        AvoidsArbitraryIrreducibles F act A →
        A.HasFiniteRelabelOrbit act) :
    TreeLike.FiniteClassHasCoherentEPPA act
      (fun {α : Type (max u v)} (A : Structure L α) =>
        AvoidsArbitraryIrreducibles F act A) := by
  intro α hα A hAvoid
  obtain ⟨β, hβ, B, ι, hAvoidB, hCoherent, _hFaith⟩ :=
    arbitraryIrreducibleFree_faithfulCoherentEPPA
      F act A (hOrbit A hAvoid) hAvoid
  exact ⟨β, hβ, B, ι, hAvoidB, hCoherent⟩

/-- In the survey's ordinary-language setting choose a finite group
acting trivially on relation and function symbols. This includes the
trivial group, and yields coherent EPPA for **arbitrary** sets of
forbidden irreducibles, rather than only finite forbidden families. -/
theorem arbitraryIrreducibleForbiddenClass_hasCoherentEPPA_trivialAction
    [Finite Γ]
    (F : ArbitraryIrreducibleFamily.{u,v} L) :
    TreeLike.FiniteClassHasCoherentEPPA
      (Language.Action.trivial L Γ)
      (fun {α : Type (max u v)} (A : Structure L α) =>
        AvoidsArbitraryIrreducibles F
          (Language.Action.trivial L Γ) A) := by
  apply arbitraryIrreducibleForbiddenClass_hasCoherentEPPA
    F (Language.Action.trivial L Γ)
  intro α hα A hAvoid
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

/-- A forbidden irreducible family may also depend on the interpretation
of arbitrarily many fixed nullary relation symbols. -/
def AvoidsArbitraryIrreduciblesWithNullaries
    {Z : Type x}
    (F : (ν : Z → Prop) → ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    {α : Type (max u v)}
    (A : WithFixedNullaryRelations L Z α) : Prop :=
  AvoidsArbitraryIrreducibles (F A.nullary) act A.positive

/-- Coherent EPPA for full survey-language classes forbidding arbitrary
(possibly infinite) irreducible families, with profile-dependent
forbidden patterns and ordinary fixed nullary relation symbols. -/
theorem arbitraryIrreducibleForbidden_withNullaries_hasCoherentEPPA
    {Z : Type x}
    (F : (ν : Z → Prop) → ArbitraryIrreducibleFamily.{u,v} L)
    (act : L.Action Γ)
    (hOrbit :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        AvoidsArbitraryIrreduciblesWithNullaries F act A →
          A.positive.HasFiniteRelabelOrbit act) :
    FullFixedNullaryClassHasCoherentEPPA act
      (fun {α : Type (max u v)}
        (A : WithFixedNullaryRelations L Z α) =>
          AvoidsArbitraryIrreduciblesWithNullaries F act A) := by
  intro α hα A hAvoid
  obtain ⟨β, hβ, B, ι, hAvoidB, hCoherent, _hFaith⟩ :=
    arbitraryIrreducibleFree_faithfulCoherentEPPA
      (F A.nullary) act A.positive (hOrbit A hAvoid) hAvoid
  exact ⟨β, hβ, ⟨B, A.nullary⟩, ⟨ι, rfl⟩,
    hAvoidB, hCoherent⟩

/-- Ordinary-language, all-nullary version without orbit hypotheses. -/
theorem arbitraryIrreducibleForbidden_withNullaries_hasCoherentEPPA_trivialAction
    {Z : Type x}
    [Finite Γ]
    (F : (ν : Z → Prop) → ArbitraryIrreducibleFamily.{u,v} L) :
    FullFixedNullaryClassHasCoherentEPPA
      (Language.Action.trivial L Γ)
      (fun {α : Type (max u v)}
        (A : WithFixedNullaryRelations L Z α) =>
          AvoidsArbitraryIrreduciblesWithNullaries
            F (Language.Action.trivial L Γ) A) := by
  apply arbitraryIrreducibleForbidden_withNullaries_hasCoherentEPPA
    F (Language.Action.trivial L Γ)
  intro α hα A hAvoid
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

end IrreducibleForb
end SurveyEPPA

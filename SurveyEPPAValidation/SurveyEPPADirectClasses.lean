import SurveyEPPAClassNullaryDirect

/-!
# Direct coherent/ordinary EPPA corollaries for the Ramsey survey

All Those EPPA Classes proves finite coherent, irreducible-structure faithful
EPPA witnesses for unary-function languages under a finite symbol-relabel
orbit. This file packages class-level consequences, without strengthening
the library's homomorphism convention, finite-orbit condition, or language
assumptions.

The survey uses a fixed language. Its nullary relation symbols are modeled
by fixed truth-value profiles in SurveyEPPANullary. The full class of such
structures therefore has coherent EPPA for any (possibly infinite) set of
fixed nullary symbols.

The completion lemmas below expose the exact local operation already used
by the verified locally finite EPPA transfer proof: a genuine
automorphism-preserving strong completion transports both EPPA and coherent
EPPA when the distinguished source structure is irreducible.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- All finite positive-arity relation/unary-function structures have
coherent EPPA, assuming every finite input has finite Γ-relabel orbit.
This is the exact class-level version of the library's unrestricted
faithful coherent EPPA theorem. -/
theorem allFiniteUnaryStructures_coherentEPPA_of_finiteOrbit
    (act : L.Action Γ)
    (hOrbit :
      ∀ {α : Type (max u v)} [Finite α] (A : Structure L α),
        A.HasFiniteRelabelOrbit act) :
    TreeLike.FiniteClassHasCoherentEPPA act
      (fun {α : Type (max u v)} (_ : Structure L α) => True) := by
  intro α hα A _hA
  obtain ⟨β, hβ, B, ι, hCoherent, _hFaith⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA
      act A (hOrbit A)
  exact ⟨β, hβ, B, ι, True.intro, hCoherent⟩

/-- The finite-orbit hypothesis is automatic for a *finite* group of
permutations of the language, even if the language has infinitely
many symbols. This also handles the one-element group. -/
theorem allFiniteUnaryStructures_coherentEPPA_finiteAction
    [Finite Γ]
    (act : L.Action Γ) :
    TreeLike.FiniteClassHasCoherentEPPA act
      (fun {α : Type (max u v)} (_ : Structure L α) => True) := by
  apply allFiniteUnaryStructures_coherentEPPA_of_finiteOrbit act
  intro α hα A
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

/-- The full fixed-language class (including arbitrary fixed nullary
relation symbols) has coherent EPPA. This is the class-level form of
the survey's Theorem thm:nreppa and its following sentence. -/
theorem allFiniteUnaryStructures_withFixedNullaries_coherentEPPA
    [Finite Γ]
    (Z : Type x) :
    FullFixedNullaryClassHasCoherentEPPA
      (Language.Action.trivial L Γ)
      (fun {α : Type (max u v)}
        (_ : WithFixedNullaryRelations L Z α) => True) := by
  intro α hα A _hA
  obtain ⟨β, hβ, B, ι, hCoherent, _hFaith⟩ :=
    unrestrictedEPPA_withNullaries_trivialAction A
  exact ⟨β, hβ, B, ι, True.intro, hCoherent⟩

/-- A genuinely automorphism-preserving strong completion transports
ordinary EPPA for an irreducible distinguished source. Ordinary
completions need not admit the necessary automorphism lift. -/
theorem ordinaryEPPA_of_automorphismPreservingStrongCompletion
    {α β δ : Type (max u v)}
    (act : L.Action Γ)
    (A : Structure L α) (hIrr : A.IsIrreducible)
    {B : Structure L β} {C : Structure L δ}
    (ι : Structure.Embedding act A B)
    (hEPPA : Structure.IsEPPAWitness act ι)
    (c : Structure.AutomorphismPreservingStrongCompletion act B C) :
    Structure.IsEPPAWitness act
      (c.completedEmbedding ι hIrr) := by
  exact c.preservesEPPA_of_irreducible ι hIrr hEPPA

/-- The coherent analogue: the compatible automorphism-group lift
preserves the entire coherent system of partial-automorphism
extensions. There is no claim that strong completions without the
automorphism-preserving condition suffice. -/
theorem coherentEPPA_of_automorphismPreservingStrongCompletion
    {α β δ : Type (max u v)}
    (act : L.Action Γ)
    (A : Structure L α) (hIrr : A.IsIrreducible)
    {B : Structure L β} {C : Structure L δ}
    (ι : Structure.Embedding act A B)
    (hCoherent : Structure.IsCoherentEPPAWitness act ι)
    (c : Structure.AutomorphismPreservingStrongCompletion act B C) :
    Structure.IsCoherentEPPAWitness act
      (c.completedEmbedding ι hIrr) := by
  exact c.preservesCoherentEPPA_of_irreducible
    ι hIrr hCoherent

/-! ## Coherence really implies EPPA

The survey's current definition of a coherent witness inadvertently omits
the requirement that the selected automorphisms extend the partial maps.
The EPPA library's coherent-extension structure includes that requirement,
and the corresponding implication is now exposed at both witness and
full-class levels. This is *not* derivable from the printed coherence
composition equation alone.
-/

/-- A genuine coherent extension of every partial automorphism is in
particular an ordinary EPPA extension. -/
theorem coherentEPPAWitness_implies_EPPA
    {α β : Type (max u v)}
    (act : L.Action Γ)
    {A : Structure L α} {B : Structure L β}
    (ι : Structure.Embedding act A B)
    (h : Structure.IsCoherentEPPAWitness act ι) :
    Structure.IsEPPAWitness act ι := by
  obtain ⟨c⟩ := h
  exact c.isEPPAWitness act

/-- Coherent EPPA of any class implies its ordinary EPPA. This uses
the full extension-specification field, not just the compatibility
equation for coherent triples. -/
theorem coherentEPPAClass_implies_EPPA
    (act : L.Action Γ)
    (E : {α : Type (max u v)} → Structure L α → Prop)
    (hE : TreeLike.FiniteClassHasCoherentEPPA act E) :
    TreeLike.FiniteClassHasEPPA act E := by
  intro α hα A hA
  obtain ⟨β, hβ, B, ι, hEB, hCoherent⟩ := hE A hA
  exact ⟨β, hβ, B, ι, hEB,
    coherentEPPAWitness_implies_EPPA act ι hCoherent⟩

/-- Same implication for arbitrary fixed nullary-relational profiles,
even when class membership depends on the complete profile. -/
theorem coherentEPPAFullNullaryClass_implies_EPPA
    (act : L.Action Γ)
    (E : {α : Type (max u v)} →
      WithFixedNullaryRelations L Z α → Prop)
    (hE : FullFixedNullaryClassHasCoherentEPPA act E) :
    FullFixedNullaryClassHasEPPA act E := by
  intro α hα A hA
  obtain ⟨β, hβ, B, ι, hEB, hCoherent⟩ := hE A hA
  exact ⟨β, hβ, B, ι, hEB,
    coherentEPPAWitness_implies_EPPA
      act ι.positive hCoherent⟩

end SurveyEPPA

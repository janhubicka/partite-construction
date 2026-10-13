import SurveyEPPAClassNullary

/-!
# Direct full-class interface for EPPA with fixed nullary relations

The preceding file indexed each class by its nullary truth-value profile
ν : Z → Prop. Here we package the EXACT same information in the more
familiar mathematical presentation: a class is a predicate on the full
split-language structures, and its embeddings must preserve every nullary
predicate. The strong amalgamation condition is checked independently
inside each fixed profile (amalgamations of distinct profiles cannot exist).

We use the verified per-profile locally finite theorem to derive the direct
class-level statement from ambient EPPA, heredity, strong amalgamation,
irreducibility and the survey's INTERNAL-FULL-COPY local completion criterion.
This prevents an unnoticed assumption that class membership ignores nullary
relations. No part of the witness construction is re-axiomatized.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {Z : Type x}

/-- A hereditary finite strong-amalgamation class of split-language
structures, stated with a single full-language membership predicate.
All strong-amalgamation certificates are within one nullary profile:
this is forced by the definition of an embedding of full structures. -/
structure FullFixedNullaryStrongAmalgamationClass
    (act : L.Action Γ) (Z : Type x) where
  mem : {V : Type (max u v)} → WithFixedNullaryRelations L Z V → Prop
  finite_of_mem :
    ∀ {V : Type (max u v)} (A : WithFixedNullaryRelations L Z V),
      mem A → Finite V
  hereditary :
    ∀ (ν : Z → Prop)
      {V W : Type (max u v)}
      {A : Structure L V} {B : Structure L W}
      (e : Structure.Embedding act A B),
      mem ⟨B, ν⟩ → mem ⟨A, ν⟩
  strong_amalgamate :
    ∀ (ν : Z → Prop)
      {I X Y : Type (max u v)}
      {D : Structure L I}
      {B₁ : Structure L X}
      {B₂ : Structure L Y}
      (f : Structure.Embedding act D B₁)
      (g : Structure.Embedding act D B₂),
      mem ⟨D, ν⟩ → mem ⟨B₁, ν⟩ → mem ⟨B₂, ν⟩ →
      ∃ (T : Type (max u v)) (_ : Finite T) (C : Structure L T),
        mem ⟨C, ν⟩ ∧
        ∃ (j₁ : Structure.Embedding act B₁ C)
          (j₂ : Structure.Embedding act B₂ C),
          j₁.comp f = j₂.comp g ∧
          (∀ (b₁ : X) (b₂ : Y),
            j₁ b₁ = j₂ b₂ →
              ∃ d : I, f d = b₁ ∧ g d = b₂)

namespace FullFixedNullaryStrongAmalgamationClass

variable {act : L.Action Γ}

/-- Extract the ordinary positive-arity hereditary strong-amalgamation
class at exactly the specified interpretation of nullary predicates. -/
def slice
    (K : FullFixedNullaryStrongAmalgamationClass act Z)
    (ν : Z → Prop) :
    TreeLike.HereditaryFiniteStrongAmalgamationClass act where
  mem := fun A => K.mem ⟨A, ν⟩
  finite_of_mem := by
    intro V A hA
    exact K.finite_of_mem ⟨A, ν⟩ hA
  hereditary := by
    intro V W D B e hB
    exact K.hereditary ν e hB
  strong_amalgamate := by
    intro I X Y D B₁ B₂ f g hD hB₁ hB₂
    exact K.strong_amalgamate ν f g hD hB₁ hB₂

end FullFixedNullaryStrongAmalgamationClass

/-- EPPA for an arbitrary full split-language class, without demanding that
membership be independent of nullary truth assignments. -/
def FullFixedNullaryClassHasEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α), E A →
      ∃ (β : Type (max u v)) (_ : Finite β)
        (B : WithFixedNullaryRelations L Z β)
        (ι : FixedNullaryEmbedding act A B),
        E B ∧ Structure.IsEPPAWitness act ι.positive

/-- Coherent EPPA for the same general full class. -/
def FullFixedNullaryClassHasCoherentEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : WithFixedNullaryRelations L Z α), E A →
      ∃ (β : Type (max u v)) (_ : Finite β)
        (B : WithFixedNullaryRelations L Z β)
        (ι : FixedNullaryEmbedding act A B),
        E B ∧ IsCoherentFixedNullaryEPPAWitness act ι

/-- An EPPA-witness preserving nullary relations for the full class already
yields ordinary EPPA in each fixed-nullary slice. -/
theorem fullClassEPPA_implies_eachSliceEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop)
    (hE : FullFixedNullaryClassHasEPPA act E)
    (ν : Z → Prop) :
    TreeLike.FiniteClassHasEPPA act
      (fun {V : Type (max u v)} (A : Structure L V) => E ⟨A, ν⟩) := by
  intro α hα A hEA
  obtain ⟨β, hβ, B, ι, hEB, hEPPA⟩ := hE ⟨A, ν⟩ hEA
  rcases B with ⟨B, ρ⟩
  have hν : ν = ρ := ι.nullary_eq
  cases hν
  exact ⟨β, hβ, B, ι.positive, hEB, hEPPA⟩

/-- Similarly, coherent ambient EPPA restricts to each nullary slice. -/
theorem fullClassCoherentEPPA_implies_eachSliceCoherentEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop)
    (hE : FullFixedNullaryClassHasCoherentEPPA act E)
    (ν : Z → Prop) :
    TreeLike.FiniteClassHasCoherentEPPA act
      (fun {V : Type (max u v)} (A : Structure L V) => E ⟨A, ν⟩) := by
  intro α hα A hEA
  obtain ⟨β, hβ, B, ι, hEB, hEPPA⟩ := hE ⟨A, ν⟩ hEA
  rcases B with ⟨B, ρ⟩
  have hν : ν = ρ := ι.nullary_eq
  cases hν
  exact ⟨β, hβ, B, ι.positive, hEB, hEPPA⟩

/-- THE SURVEY'S CLASS-LEVEL EPPA TRANSFER WITH NULLARY RELATIONS.
All class-membership assumptions refer to the *whole* split language;
neither K nor E is assumed to ignore nullary relations. Local finiteness
is the survey's internal full-copy version (not the EPPA paper's).
Only the relevant equal-profile pairs (A,B₀) need be checked. -/
theorem locallyFiniteEPPA_fullClass_withFixedNullaries
    (act : L.Action Γ)
    (K : FullFixedNullaryStrongAmalgamationClass act Z)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        K.mem A → E A)
    (hE : FullFixedNullaryClassHasEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        K.mem A → A.positive.IsIrreducible)
    (hLocal :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem ⟨A, ν⟩ → E ⟨B₀, ν⟩ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (K.slice ν).toAmalgamationClass) :
    FullFixedNullaryClassHasEPPA act K.mem := by
  let KS : NullarySlicedHereditaryStrongAmalgamationClass act Z :=
    fun ν => K.slice ν
  let ES : (ν : Z → Prop) →
      {V : Type (max u v)} → Structure L V → Prop :=
    fun ν _ A => E ⟨A, ν⟩
  have hSubS :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (KS ν).toAmalgamationClass.mem A → ES ν A := by
    intro ν α hα A hA
    exact hSub ⟨A, ν⟩ hA
  have hES :
      ∀ ν : Z → Prop, TreeLike.FiniteClassHasEPPA act (ES ν) := by
    intro ν
    exact fullClassEPPA_implies_eachSliceEPPA act E hE ν
  have hIrrS :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (KS ν).toAmalgamationClass.mem A → A.IsIrreducible := by
    intro ν α hα A hA
    exact hIrr ⟨A, ν⟩ hA
  have hLocalS :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        (KS ν).toAmalgamationClass.mem A → ES ν B₀ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (KS ν).toAmalgamationClass := by
    intro ν α β hα hβ A B₀ hKA hEB
    exact hLocal ν A B₀ hKA hEB
  intro α hα A hKA
  obtain ⟨β, hβ, B, ι, hKB, hEPPA⟩ :=
    (locallyFiniteEPPA_withFixedNullaryRelations
      act KS ES hSubS hES hIrrS hLocalS) A hKA
  exact ⟨β, hβ, B, ι, hKB, hEPPA⟩

/-- Coherent form of the same full-language theorem, with no additional
coherent completion assumption. -/
theorem locallyFiniteCoherentEPPA_fullClass_withFixedNullaries
    (act : L.Action Γ)
    (K : FullFixedNullaryStrongAmalgamationClass act Z)
    (E : {V : Type (max u v)} →
      WithFixedNullaryRelations L Z V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        K.mem A → E A)
    (hE : FullFixedNullaryClassHasCoherentEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : WithFixedNullaryRelations L Z α),
        K.mem A → A.positive.IsIrreducible)
    (hLocal :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem ⟨A, ν⟩ → E ⟨B₀, ν⟩ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (K.slice ν).toAmalgamationClass) :
    FullFixedNullaryClassHasCoherentEPPA act K.mem := by
  let KS : NullarySlicedHereditaryStrongAmalgamationClass act Z :=
    fun ν => K.slice ν
  let ES : (ν : Z → Prop) →
      {V : Type (max u v)} → Structure L V → Prop :=
    fun ν _ A => E ⟨A, ν⟩
  have hSubS :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (KS ν).toAmalgamationClass.mem A → ES ν A := by
    intro ν α hα A hA
    exact hSub ⟨A, ν⟩ hA
  have hES :
      ∀ ν : Z → Prop, TreeLike.FiniteClassHasCoherentEPPA act (ES ν) := by
    intro ν
    exact fullClassCoherentEPPA_implies_eachSliceCoherentEPPA act E hE ν
  have hIrrS :
      ∀ (ν : Z → Prop) {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        (KS ν).toAmalgamationClass.mem A → A.IsIrreducible := by
    intro ν α hα A hA
    exact hIrr ⟨A, ν⟩ hA
  have hLocalS :
      ∀ (ν : Z → Prop)
        {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        (KS ν).toAmalgamationClass.mem A → ES ν B₀ →
        HasSurveyLocallyFiniteAutomorphismPreservingCompletion
          act A B₀ (KS ν).toAmalgamationClass := by
    intro ν α β hα hβ A B₀ hKA hEB
    exact hLocal ν A B₀ hKA hEB
  intro α hα A hKA
  obtain ⟨β, hβ, B, ι, hKB, hCoherent⟩ :=
    (locallyFiniteCoherentEPPA_withFixedNullaryRelations
      act KS ES hSubS hES hIrrS hLocalS) A hKA
  exact ⟨β, hβ, B, ι, hKB, hCoherent⟩

end SurveyEPPA

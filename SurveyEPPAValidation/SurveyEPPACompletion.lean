import SurveyEPPA

/-!
# Proposition 11.3 with the survey's exact-fibre completion convention

The EPPA paper calls an inclusion-preserving map a homomorphism, whereas the
survey requires exact images of all set-valued function fibres. These notions
differ in general but their HOMOMORPHISM-EMBEDDING notions coincide for unary
functions (proved in SurveyEPPA.lean). This file upgrades the actual survey
completions, rather than merely renaming the paper's proposition.

No automorphism-preserving completion is inferred here: that is a distinct,
strictly stronger condition used in the locally finite EPPA transfer.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- Existence of a survey-style completion, requiring exact function fibres
throughout the homomorphism, not merely inclusion. -/
def HasSurveyCompletion
    (act : L.Action Γ)
    (K : TreeLike.FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (B : Structure L W),
    K.mem B ∧
      ∃ f : Structure.Homomorphism act A B,
        IsSurveyHomomorphismEmbedding act f

/-- A survey completion additionally injective on its entire carrier. -/
def HasSurveyStrongCompletion
    (act : L.Action Γ)
    (K : TreeLike.FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (B : Structure L W),
    K.mem B ∧
      ∃ f : Structure.Homomorphism act A B,
        IsSurveyHomomorphismEmbedding act f ∧
          Function.Injective f.toFun

/-- Ordinary survey completion is equivalent to the EPPA paper completion
when all function symbols are unary. -/
theorem surveyCompletion_iff_paperCompletion
    (act : L.Action Γ)
    (K : TreeLike.FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V) :
    HasSurveyCompletion act K A ↔ K.HasCompletion A := by
  constructor
  · rintro ⟨W, hW, B, hB, f, hf⟩
    exact ⟨W, hW, B, hB, f, hf.1⟩
  · rintro ⟨W, hW, B, hB, f, hf⟩
    exact ⟨W, hW, B, hB, f,
      (paperHomEmbedding_iff_surveyHomEmbedding act f).mp hf⟩

/-- Strong survey completion is equivalent to the paper's injective HE
completion, with no automorphism lift implied. -/
theorem surveyStrongCompletion_iff_paperStrongCompletion
    (act : L.Action Γ)
    (K : TreeLike.FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V) :
    HasSurveyStrongCompletion act K A ↔ K.HasStrongCompletion A := by
  constructor
  · rintro ⟨W, hW, B, hB, f, hf, hInjective⟩
    exact ⟨W, hW, B, hB, f, hf.1, hInjective⟩
  · rintro ⟨W, hW, B, hB, f, hf, hInjective⟩
    exact ⟨W, hW, B, hB, f,
      (paperHomEmbedding_iff_surveyHomEmbedding act f).mp hf,
      hInjective⟩

/-- Proposition 11.3, literally for the SURVEY convention of
homomorphism-embedding, derived from the fully proved public API. -/
theorem surveyCompletion_iff_strong
    (act : L.Action Γ)
    (K : TreeLike.HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V] (A : Structure L V) :
    HasSurveyCompletion act K.toAmalgamationClass A ↔
      HasSurveyStrongCompletion act K.toAmalgamationClass A := by
  constructor
  · intro h
    have hPaper : K.toAmalgamationClass.HasCompletion A :=
      (surveyCompletion_iff_paperCompletion
        act K.toAmalgamationClass A).mp h
    have hStrong : K.toAmalgamationClass.HasStrongCompletion A :=
      (MainTheorems.completionIffStrong act K A).mp hPaper
    exact (surveyStrongCompletion_iff_paperStrongCompletion
      act K.toAmalgamationClass A).mpr hStrong
  · intro h
    have hStrong : K.toAmalgamationClass.HasStrongCompletion A :=
      (surveyStrongCompletion_iff_paperStrongCompletion
        act K.toAmalgamationClass A).mp h
    have hPaper : K.toAmalgamationClass.HasCompletion A :=
      (MainTheorems.completionIffStrong act K A).mpr hStrong
    exact (surveyCompletion_iff_paperCompletion
      act K.toAmalgamationClass A).mpr hPaper

end SurveyEPPA

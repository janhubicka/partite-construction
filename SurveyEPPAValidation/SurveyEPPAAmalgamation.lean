import SurveyEPPA

/-!
# Literal amalgamation for the survey's EPPA + JEP observation

SurveyEPPA.lean establishes agreement of the two amalgamating embeddings
both on every vertex and on the Γ-language component. The library's
amalgamation interface demands EQUALITY of the resulting embeddings.
This file closes that representation gap instead of treating agreement of
the visible fields as definitional equality.
-/

namespace SurveyEPPA
open AllThoseEPPA

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- Γ-embeddings are completely determined by their language component
and their action on vertices. All remaining structure fields are proofs,
which are propositionally irrelevant once these data agree. -/
theorem embedding_eq_of_lang_and_apply
    {V W : Type (max u v)}
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f g : Structure.Embedding act A B)
    (hLang : f.lang = g.lang)
    (hPoint : ∀ a, f a = g a) :
    f = g := by
  cases f with
  | mk fL fA fInj fRel fFunc =>
    cases g with
    | mk gL gA gInj gRel gFunc =>
      change fL = gL at hLang
      change ∀ a, fA a = gA a at hPoint
      have hFun : fA = gA := by
        funext a
        exact hPoint a
      cases hLang
      cases hFun
      rfl

/-- The survey's ordinary amalgamation property as a literal commuting
diagram of Γ-embeddings, not merely agreement of individual components. -/
def HasExactAmalgamation
    (act : L.Action Γ)
    (E : {V : Type (max u v)} → Structure L V → Prop) : Prop :=
  ∀ {α β₁ β₂ : Type (max u v)}
    [Finite α] [Finite β₁] [Finite β₂]
    (A : Structure L α)
    (B₁ : Structure L β₁) (B₂ : Structure L β₂),
    E A → E B₁ → E B₂ →
    (i₁ : Structure.Embedding act A B₁) →
    (i₂ : Structure.Embedding act A B₂) →
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (D : Structure L δ)
      (j₁ : Structure.Embedding act B₁ D)
      (j₂ : Structure.Embedding act B₂ D),
      E D ∧ j₁.comp i₁ = j₂.comp i₂

/-- Literal form of the survey observation:
EPPA + joint embedding implies amalgamation, for genuine Γ-embeddings,
without ever assuming amalgamation of the ambient class. -/
theorem eppa_and_jointEmbedding_imply_exactAmalgamation
    (act : L.Action Γ)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hJEP : HasJointEmbedding act E)
    (hEPPA : TreeLike.FiniteClassHasEPPA act E) :
    HasExactAmalgamation act E := by
  intro α β₁ β₂ hα hβ₁ hβ₂
    A B₁ B₂ hA hB₁ hB₂ i₁ i₂
  obtain ⟨δ, hδ, D, j₁, j₂, hD, hLang, hPoint⟩ :=
    (eppa_and_jointEmbedding_imply_amalgamation act E hJEP hEPPA)
      A B₁ B₂ hA hB₁ hB₂ i₁ i₂
  exact ⟨δ, hδ, D, j₁, j₂, hD,
    embedding_eq_of_lang_and_apply
      act (j₁.comp i₁) (j₂.comp i₂) hLang hPoint⟩

end SurveyEPPA

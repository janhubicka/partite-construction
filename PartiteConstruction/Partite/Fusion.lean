import PartiteConstruction.Partite.Projection

/-! # Backward induction through a finite sequence of pictures

This lemma is independent of how the pictures are built. The local hypotheses
are explicit; this does not assert existence of the Picture Lemma's witnesses.
It applies unchanged to the non-induced and induced constructions.
-/
namespace StructuralRamsey.Partite

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v} {U : Type w}
variable (A : RelStructure L U) {V : ℕ → Type z}
variable (B : (i : ℕ) → System L P (V i)) (α : ℕ → U → P) (κ : Type t)

/-- After i steps, colours have been homogenized on the first i projections. -/
theorem backwardFusion (n : ℕ)
    (step : ∀ i < n,
      ∀ χ : ProjectedEmbedding A (B (i + 1)) (α i) → κ,
      ∃ f : Embedding (B i) (B (i + 1)),
        ∀ e₁ e₂ : ProjectedEmbedding A (B i) (α i),
          χ (e₁.comp f) = χ (e₂.comp f))
    (χ : RelStructure.Embedding A (B n).toRelStructure → κ) :
    ∃ f : Embedding (B 0) (B n), ∀ i < n,
      ∀ e₁ e₂ : ProjectedEmbedding A (B 0) (α i),
        χ (f.toEmbedding.comp e₁.val) = χ (f.toEmbedding.comp e₂.val) := by
  induction n with
  | zero =>
      exact ⟨Embedding.id (B 0), fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
      obtain ⟨g, hg⟩ := step n (Nat.lt_succ_self n) (fun e => χ e.val)
      obtain ⟨f, hf⟩ := ih (fun i hi => step i (Nat.lt_succ_of_lt hi))
        (fun e => χ (g.toEmbedding.comp e))
      refine ⟨g.comp f, ?_⟩
      intro i hi e₁ e₂
      by_cases hin : i < n
      · simpa only [Embedding.comp, RelStructure.Embedding.comp_assoc] using hf i hin e₁ e₂
      · have hieq : i = n := by omega
        subst i
        exact hg (e₁.comp f) (e₂.comp f)

end StructuralRamsey.Partite

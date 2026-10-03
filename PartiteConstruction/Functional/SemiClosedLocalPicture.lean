import PartiteConstruction.Functional.SemiClosedPictureCore

/-! # Arbitrary-projection semi-closed Picture lemma

This is the corrected local input for the recursive partite construction.

The little picture produced here is deliberately *not* required to be
U-transversal.  It is only D-partite and satisfies the half-closed Ramsey
property.  The following singleton-valued partite construction repairs that
little picture to the next U-transversal stage.

The overlap consists exactly of vertices occurring in relevant closed A-copies.
The closed Hales--Jewett partite lemma is applied to this overlap.  Each chosen
overlap copy is then extended to an ordinary copy of the whole current stage,
while selectedCopy_closed guarantees that the relevant A-subcopies remain
closed.
-/
namespace StructuralRamsey.Partite.SemiClosed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V : Type v}

/-- Correct arbitrary-projection little Picture lemma for finite partial
functions with explicit domain/root relations.

There is intentionally no U-transversality conclusion for O. -/
theorem pictureLemma
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hBPartite : B.IsPartiteOver D)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X)
      (O : Partite.System L.withFunctionDomains.graph P X),
      O.IsPartiteOver D ∧
      Partite.HalfClosedArrow
        (A := Partite.Recursive.profile A D α)
        (B := B) (D := O) κ := by
  classical
  let R := restriction A D B α
  have hRPartite : R.IsPartiteOver A :=
    restriction_isPartiteOver A D B α hBPartite
  have hRSingle : R.FunctionOutputSingleValued :=
    restriction_singleValued A D B α hBsingle
  have hRU : R.FunctionOutputTransversal :=
    hRSingle.uTransversal
  obtain ⟨N, hN, _hPowerU, hArrow⟩ :=
    Partite.Closed.Induced.partiteLemma
      (A := A) (B := R) hRPartite hRU κ
  let E := Partite.Induced.power R N
  let O := build A D B α E
  have hEPartite : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hRPartite hN
  have hCorePartite :
      (E.relabel α.toFunctionEmbedding).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hEPartite α
  have hOPartite : O.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun f : Partite.Closed.Embedding R E =>
        (attachingMap A D B α f).1)
      hBPartite hCorePartite
  refine ⟨Vertex A D B α E, inferInstance, O, hOPartite, ?_⟩
  intro χ
  let default : κ :=
    Classical.choice (inferInstance : Nonempty κ)
  let θ :
      Partite.Closed.Embedding (Partite.transversal A) E → κ :=
    fun d =>
      if hd : CoreLiftable A D B α E d then
        χ (liftCore A D B α E
          hAtotal hBroot hBsingle d hd)
      else default
  obtain ⟨f, hf⟩ := hArrow θ
  let maps :=
    fun g : Partite.Closed.Embedding R E =>
      attachingMap A D B α g
  let β : Partite.Embedding B O :=
    Partite.Attachment.copyEmbedding
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g => (maps g).1) f
  let projected
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      Partite.Closed.ProjectedEmbedding
        A B (fun a => α a) :=
    Partite.Recursive.profileEmbeddingToProjected e
  let lift
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) O :=
    selectedLift A D B α E
      hAtotal hBroot hBsingle f (projected e)
  refine ⟨β, lift, ?_, ?_⟩
  · intro e x
    rfl
  · intro e₁ e₂
    let p₁ := projected e₁
    let p₂ := projected e₂
    let r₁ : Partite.Closed.Embedding
        (Partite.transversal A) R :=
      restrictRelevant A D B α p₁
    let r₂ : Partite.Closed.Embedding
        (Partite.transversal A) R :=
      restrictRelevant A D B α p₂
    let d₁ : Partite.Closed.Embedding
        (Partite.transversal A) E :=
      Partite.Closed.Embedding.comp f r₁
    let d₂ : Partite.Closed.Embedding
        (Partite.transversal A) E :=
      Partite.Closed.Embedding.comp f r₂
    have hd₁ : CoreLiftable A D B α E d₁ :=
      ⟨f, p₁, rfl⟩
    have hd₂ : CoreLiftable A D B α E d₂ :=
      ⟨f, p₂, rfl⟩
    have hlift₁ :
        liftCore A D B α E
            hAtotal hBroot hBsingle d₁ hd₁ =
          lift e₁ := by
      apply Partite.Closed.Embedding.ext
      intro a
      rw [liftCore_apply, selectedLift_core]
      rfl
    have hlift₂ :
        liftCore A D B α E
            hAtotal hBroot hBsingle d₂ hd₂ =
          lift e₂ := by
      apply Partite.Closed.Embedding.ext
      intro a
      rw [liftCore_apply, selectedLift_core]
      rfl
    have hθ₁ : θ d₁ = χ (lift e₁) := by
      simp only [θ, dif_pos hd₁]
      rw [hlift₁]
    have hθ₂ : θ d₂ = χ (lift e₂) := by
      simp only [θ, dif_pos hd₂]
      rw [hlift₂]
    have hmono : θ d₁ = θ d₂ := by
      exact hf r₁ r₂
    exact hθ₁.symm.trans (hmono.trans hθ₂)

end StructuralRamsey.Partite.SemiClosed.Picture

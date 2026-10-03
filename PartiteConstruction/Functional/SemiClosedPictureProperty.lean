import PartiteConstruction.Functional.SemiClosedPictureCore

/-! # Arbitrary-projection semi-closed Picture lemma

This is the corrected local "little picture" used by the recursive partite
construction.  The output is only required to remain D-partite; it is not
claimed to be U-transversal.

The Hales--Jewett core is built on the overlap covered by relevant closed
A-copies.  A default colour is assigned to core A-letters which do not come
from such a copy.  On liftable letters, the selected-copy closure theorem
turns the core letter back into a closed profile copy in the little picture.
-/
namespace StructuralRamsey.Partite.SemiClosed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- The arbitrary-projection little picture remains D-partite. -/
theorem build_isPartiteOver
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hB : B.IsPartiteOver D)
    (hE : E.IsPartiteOver A) :
    (build A D B α E).IsPartiteOver D := by
  have hCore :
      (E.relabel α.toFunctionEmbedding).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hE α
  exact
    Partite.Attachment.attach_isPartiteOver
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun f : Partite.Closed.Embedding
        (restriction A D B α) E =>
          (attachingMap A D B α f).1)
      hB hCore

/-- A closed core Ramsey arrow gives the half-closed Ramsey property required
from the little picture.  The selected B-copy itself is ordinary; every
relevant closed profile copy inside it is lifted to a closed copy. -/
theorem halfClosedProperty
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (κ : Type*) [Nonempty κ]
    (hE : Partite.Closed.Arrow
      (Partite.transversal A)
      (restriction A D B α) E κ) :
    Partite.HalfClosedArrow
      (A := Partite.Recursive.profile A D α)
      (B := B) (D := build A D B α E) κ := by
  classical
  intro χ
  let θ :
      Partite.Closed.Embedding
        (Partite.transversal A) E → κ := fun d =>
    if hd : CoreLiftable A D B α E d then
      χ (liftCore A D B α E
        hAtotal hBroot hBsingle d hd)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨f, hf⟩ := hE θ
  let β : Partite.Embedding B (build A D B α E) :=
    Partite.Attachment.copyEmbedding
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g : Partite.Closed.Embedding
        (restriction A D B α) E =>
          (attachingMap A D B α g).1)
      f
  let projected
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      Partite.Closed.ProjectedEmbedding
        A B (fun a => α a) :=
    Partite.Recursive.profileEmbeddingToProjected
      (D := D) (α := α) e
  let coreLetter
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      Partite.Closed.Embedding
        (Partite.transversal A) E :=
    Partite.Closed.Embedding.comp f
      (restrictRelevant A D B α (projected e))
  have coreLiftable
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      CoreLiftable A D B α E (coreLetter e) := by
    exact ⟨f, projected e, rfl⟩
  let lift
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) B) :
      Partite.Closed.Embedding
        (Partite.Recursive.profile A D α)
        (build A D B α E) :=
    liftCore A D B α E
      hAtotal hBroot hBsingle
      (coreLetter e) (coreLiftable e)
  refine ⟨β, lift, ?_, ?_⟩
  · intro e a
    have hLift :=
      liftCore_apply A D B α E
        hAtotal hBroot hBsingle
        (coreLetter e) (coreLiftable e) a
    have hSelected :=
      selectedLift_core A D B α E
        hAtotal hBroot hBsingle
        f (projected e) a
    calc
      lift e a =
          Partite.Attachment.coreEmbedding
            B (coveredSet A D B α)
            (E.relabel α.toFunctionEmbedding)
            (fun g : Partite.Closed.Embedding
              (restriction A D B α) E =>
                (attachingMap A D B α g).1)
            (coreLetter e a) := hLift
      _ =
          Partite.Attachment.coreEmbedding
            B (coveredSet A D B α)
            (E.relabel α.toFunctionEmbedding)
            (fun g : Partite.Closed.Embedding
              (restriction A D B α) E =>
                (attachingMap A D B α g).1)
            (f (restrictRelevant A D B α (projected e) a)) := rfl
      _ =
          selectedLift A D B α E
            hAtotal hBroot hBsingle
            f (projected e) a := hSelected.symm
      _ = β (e a) := rfl
  · intro e₁ e₂
    have hθ
        (e : Partite.Closed.Embedding
          (Partite.Recursive.profile A D α) B) :
        θ (coreLetter e) = χ (lift e) := by
      have hcl := coreLiftable e
      simp only [θ, dif_pos hcl, lift]
      exact congrArg χ
        (liftCore_unique A D B α E
          hAtotal hBroot hBsingle
          (coreLetter e) _ _)
    have hm :=
      hf
        (restrictRelevant A D B α (projected e₁))
        (restrictRelevant A D B α (projected e₂))
    change
      θ (coreLetter e₁) = θ (coreLetter e₂) at hm
    rw [hθ e₁, hθ e₂] at hm
    exact hm

/-- Correct arbitrary-projection Picture lemma in the partial-function/domain
encoding.  Crucially, the intermediate picture is not asserted to be
U-transversal. -/
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
  have hEPartite : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hRPartite hN
  let O := build A D B α E
  exact ⟨Vertex A D B α E, inferInstance, O,
    build_isPartiteOver A D B α E hBPartite hEPartite,
    halfClosedProperty A D B α E
      hAtotal hBroot hBsingle κ hArrow⟩

end StructuralRamsey.Partite.SemiClosed.Picture

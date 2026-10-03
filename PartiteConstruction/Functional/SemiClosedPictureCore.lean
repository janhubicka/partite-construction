import PartiteConstruction.Functional.SemiClosedPicture

/-! # Liftable core letters in the semi-closed little picture -/
namespace StructuralRamsey.Partite.SemiClosed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- On a relevant A-copy, the selected attached copy agrees with the core map
coming from the overlap embedding. -/
theorem selectedLift_core
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (f : Partite.Closed.Embedding
      (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a))
    (a : U) :
    selectedLift A D B α E hAtotal hBroot hBsingle f e a =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (f (restrictRelevant A D B α e a)) := by
  let x : coveredSet A D B α :=
    ⟨e.1 a, ⟨e, a, rfl⟩⟩
  have hcopy :=
    Partite.Attachment.copy_extends
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g : Partite.Closed.Embedding
        (restriction A D B α) E =>
          (attachingMap A D B α g).1)
      f x
  rw [selectedLift_apply]
  calc
    Partite.Attachment.copyEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        f (e.1 a) =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        ((attachingMap A D B α f) x) := hcopy
    _ =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (f (restrictRelevant A D B α e a)) := by
      congr 1
      change
        f (overlapToRestriction A D B α x) =
          f (restrictRelevant A D B α e a)
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rfl

/-- A core A-letter is relevant if it factors through one closed overlap copy
and one A-copy coming from the previous picture. -/
def CoreLiftable
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E) : Prop :=
  ∃ f : Partite.Closed.Embedding
      (restriction A D B α) E,
    ∃ e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a),
      d = Partite.Closed.Embedding.comp
        f (restrictRelevant A D B α e)

/-- Turn a liftable core letter into the corresponding closed projected copy
in the little picture. -/
noncomputable def liftCore
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (hd : CoreLiftable A D B α E d) :
    Partite.Closed.Embedding
      (Partite.Recursive.profile A D α)
      (build A D B α E) := by
  let f := Classical.choose hd
  let he := Classical.choose_spec hd
  let e := Classical.choose he
  exact
    selectedLift A D B α E
      hAtotal hBroot hBsingle f e

theorem liftCore_apply
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (hd : CoreLiftable A D B α E d)
    (a : U) :
    liftCore A D B α E hAtotal hBroot hBsingle d hd a =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (d a) := by
  let f := Classical.choose hd
  have he := Classical.choose_spec hd
  let e := Classical.choose he
  have hfac : d =
      Partite.Closed.Embedding.comp
        f (restrictRelevant A D B α e) :=
    Classical.choose_spec he
  change
    selectedLift A D B α E
      hAtotal hBroot hBsingle f e a = _
  rw [selectedLift_core]
  congr 1
  have happ := congrArg
    (fun q : Partite.Closed.Embedding
      (Partite.transversal A) E => q a) hfac
  exact happ.symm

theorem liftCore_unique
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (h₁ h₂ : CoreLiftable A D B α E d) :
    liftCore A D B α E hAtotal hBroot hBsingle d h₁ =
      liftCore A D B α E hAtotal hBroot hBsingle d h₂ := by
  apply Partite.Closed.Embedding.ext
  intro a
  rw [liftCore_apply, liftCore_apply]

end StructuralRamsey.Partite.SemiClosed.Picture

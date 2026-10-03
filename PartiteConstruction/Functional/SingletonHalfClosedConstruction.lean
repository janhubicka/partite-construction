import PartiteConstruction.Functional.SingletonClosedPicture
import PartiteConstruction.Functional.HalfClosedConstruction

/-! # Half-closed construction preserving partial-function fibres

The ordinary half-closed construction does not need its target D to be
U-transversal.  When the copied structure B is globally singleton-valued, the
initial disjoint union and every closed-alpha Picture step preserve that
stronger invariant.  Thus the output is again singleton-valued (and hence
U-transversal) even if the intermediate target D is not.

This is the repair step needed by the original two-stage recursive partite
construction.
-/
namespace StructuralRamsey.Partite.HalfClosed.Construction

open RelStructure Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A half-closed stage carrying the global partial-function invariant. -/
structure SingletonStage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : Partite.System L.graph P Vertex
  isPartite : system.IsPartiteOver D
  singleValued : system.FunctionOutputSingleValued

attribute [instance] SingletonStage.finiteVertex

/-- Ordinary-indexed initial stage, now with the stronger singleton
invariant. -/
def initialSingletonStage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    (hB : B.FunctionOutputSingleValued)
    [Finite V] [Finite P]
    [Nonempty (RelStructure.Embedding B D)] :
    SingletonStage B D where
  Vertex := Partite.HalfClosed.Initial.Index B D × V
  finiteVertex := inferInstance
  system := Partite.HalfClosed.Initial.picture B D
  isPartite := Partite.HalfClosed.Initial.isPartiteOver B D
  singleValued :=
    Partite.HalfClosed.Initial.singleValued B D hpos hB

/-- Process relevant closed projections while preserving global
singleton-valuedness. -/
theorem build_singleValued
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (S : SingletonStage B D)
    [Finite U]
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) [Fintype κ] :
    ∃ T : SingletonStage B D,
      CanonicalOn A B D S.system T.system xs κ := by
  induction xs with
  | nil =>
      refine ⟨S, ?_⟩
      intro χ
      refine ⟨Partite.Closed.Embedding.id S.system, ?_⟩
      intro α h
      exact (List.not_mem_nil h).elim
  | cons α xs ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨Y, hY, C, hPartite, hSingle, hPicture⟩ :=
        Partite.Closed.Picture.pictureLemma_singleValued
          A D T.system α.1 T.isPartite T.singleValued κ
      let R : SingletonStage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hPartite
        singleValued := hSingle
      }
      refine ⟨R, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hPicture (fun e => χ e.1)
      obtain ⟨f, hf⟩ := hT
        (fun e => χ
          (RelStructure.ClosedEmbedding.comp g.toRelClosed e))
      refine ⟨Partite.Closed.Embedding.comp g f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg
          (Partite.Closed.ProjectedEmbedding.comp e₁ f)
          (Partite.Closed.ProjectedEmbedding.comp e₂ f)
      · exact hf β hβ e₁ e₂

/-- Half-closed repair for a globally singleton-valued copied structure.
No singleton/U-transversal hypothesis is imposed on the intermediate target
D. -/
theorem inducedConstruction_singleValued
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (hB : B.FunctionOutputSingleValued)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.HalfClosedArrow A B D κ) :
    letI : Nonempty (RelStructure.Embedding B D) :=
      RelStructure.nonempty_embedding_of_halfClosedArrow
        A B D κ hRamsey
    let S₀ := initialSingletonStage B D hpos hB
    ∃ T : SingletonStage B D,
      RelStructure.ClosedArrow
        A B T.system.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    RelStructure.nonempty_embedding_of_halfClosedArrow
      A B D κ hRamsey
  let S₀ := initialSingletonStage B D hpos hB
  let xs := allRelevant A B D
  obtain ⟨T, hCanon⟩ :=
    build_singleValued A B D S₀ xs κ
  refine ⟨T, ?_⟩
  intro χ
  let projected
      (α : RelStructure.ClosedEmbedding A D)
      (hα : Relevant A B D α) :
      Partite.Closed.ProjectedEmbedding A S₀.system α := by
    let β : RelStructure.Embedding B D := Classical.choose hα
    have hrest :
        ∃ e : RelStructure.ClosedEmbedding A B,
          ∀ x, α x = β (e x) :=
      Classical.choose_spec hα
    let e : RelStructure.ClosedEmbedding A B :=
      Classical.choose hrest
    have hfac : ∀ x, α x = β (e x) :=
      Classical.choose_spec hrest
    exact initialProjectedCopy hpos B D α β e hfac
  obtain ⟨f, hf⟩ := hCanon χ
  let θ : RelStructure.ClosedEmbedding A D → κ := fun α =>
    if hα : Relevant A B D α then
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (projected α hα).1)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, lift, hlift, hmono⟩ := hRamsey θ
  let j : RelStructure.ClosedEmbedding
      B S₀.system.toRelStructure :=
    Partite.HalfClosed.Initial.copyEmbedding B D hpos β
  refine
    ⟨RelStructure.ClosedEmbedding.comp f.toRelClosed j, ?_⟩
  intro e₁ e₂
  let α₁ : RelStructure.ClosedEmbedding A D := lift e₁
  let α₂ : RelStructure.ClosedEmbedding A D := lift e₂
  have hα₁ : Relevant A B D α₁ :=
    ⟨β, e₁, hlift e₁⟩
  have hα₂ : Relevant A B D α₂ :=
    ⟨β, e₂, hlift e₂⟩
  let p₁ :=
    initialProjectedCopy hpos B D α₁ β e₁ (hlift e₁)
  let p₂ :=
    initialProjectedCopy hpos B D α₂ β e₂ (hlift e₂)
  have hm₁ :
      (⟨α₁, hα₁⟩ : RelevantEmbedding A B D) ∈ xs := by
    simp [xs]
  have hm₂ :
      (⟨α₂, hα₂⟩ : RelevantEmbedding A B D) ∈ xs := by
    simp [xs]
  have hc₁ :=
    hf ⟨α₁, hα₁⟩ hm₁ p₁ (projected α₁ hα₁)
  have hc₂ :=
    hf ⟨α₂, hα₂⟩ hm₂ p₂ (projected α₂ hα₂)
  have ht₁ :
      θ α₁ =
        χ (RelStructure.ClosedEmbedding.comp
          f.toRelClosed (projected α₁ hα₁).1) := by
    simp [θ, hα₁]
  have ht₂ :
      θ α₂ =
        χ (RelStructure.ClosedEmbedding.comp
          f.toRelClosed (projected α₂ hα₂).1) := by
    simp [θ, hα₂]
  have hpmono :
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed p₁.1) =
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed p₂.1) := by
    exact hc₁.trans
      (ht₁.symm.trans
        ((hmono e₁ e₂).trans (ht₂.trans hc₂.symm)))
  have hp₁ :
      p₁.1 = RelStructure.ClosedEmbedding.comp j e₁ := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hp₂ :
      p₂.1 = RelStructure.ClosedEmbedding.comp j e₂ := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hassoc₁ :
      RelStructure.ClosedEmbedding.comp
          (RelStructure.ClosedEmbedding.comp
            f.toRelClosed j) e₁ =
        RelStructure.ClosedEmbedding.comp
          f.toRelClosed
          (RelStructure.ClosedEmbedding.comp j e₁) := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hassoc₂ :
      RelStructure.ClosedEmbedding.comp
          (RelStructure.ClosedEmbedding.comp
            f.toRelClosed j) e₂ =
        RelStructure.ClosedEmbedding.comp
          f.toRelClosed
          (RelStructure.ClosedEmbedding.comp j e₂) := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  rw [hassoc₁, hassoc₂, ← hp₁, ← hp₂]
  exact hpmono

end StructuralRamsey.Partite.HalfClosed.Construction

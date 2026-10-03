import PartiteConstruction.Functional.SemiClosedPictureProperty
import PartiteConstruction.Functional.RootPrune
import PartiteConstruction.Functional.SingletonHalfClosedPartite

/-! # End-to-end recursive construction for partial functions

This file implements the corrected two-stage recursive partite construction.

At each ordinary projection alpha:
1. build a semi-closed little picture O.  O is D-partite and has the required
   half-closed Ramsey property, but is not required to be U-transversal;
2. apply the singleton-valued half-closed partite construction.  This produces
   the next D-partite stage with a genuine closed arrow and restores the
   global singleton-output invariant.

Thus the outer recursion carries singleton-valuedness, not transversality.
Singleton-valuedness implies the U-transversality needed in the final witness.
-/
namespace StructuralRamsey.Partite.SemiClosed.Recursive

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {U V P : Type v}

abbrev profile :=
  Partite.Recursive.profile
    (L := L.withFunctionDomains) (U := U) (P := P)

abbrev CanonicalOn :=
  Partite.Recursive.CanonicalOn
    (L := L.withFunctionDomains) (U := U) (P := P)

/-- A recursive stage for the partial-function/domain encoding. -/
structure Stage
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : Partite.System L.withFunctionDomains.graph P Vertex
  isPartite : system.IsPartiteOver D
  singleValued : system.FunctionOutputSingleValued

attribute [instance] Stage.finiteVertex

/-- Initial ordinary-copy picture, carrying singleton-valuedness. -/
def initialStage
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph P)
    [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (hBsingle : B.FunctionOutputSingleValued)
    [Nonempty (RelStructure.Embedding B D)] :
    Stage B D where
  Vertex := Partite.HalfClosed.Initial.Index B D × V
  finiteVertex := inferInstance
  system := Partite.HalfClosed.Initial.picture B D
  isPartite := Partite.HalfClosed.Initial.isPartiteOver B D
  singleValued :=
    Partite.HalfClosed.Initial.singleValued
      B D hpos.withFunctionDomains hBsingle

/-- One corrected recursive step: semi-closed little picture followed by the
closed singleton repair. -/
theorem step
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    [Finite U]
    (hpos : L.PositiveFuncArity)
    (hAtotal : A.FunctionDomainTotal)
    (hDroot : D.OutputImpliesDomain)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    {X : Type v} [Finite X]
    (S : Partite.System L.withFunctionDomains.graph P X)
    (hSPartite : S.IsPartiteOver D)
    (hSsingle : S.FunctionOutputSingleValued)
    (α : RelStructure.Embedding A D) :
    ∃ (Y : Type v) (_ : Finite Y)
      (C : Partite.System L.withFunctionDomains.graph P Y),
      C.IsPartiteOver D ∧
      C.FunctionOutputSingleValued ∧
      Partite.Closed.Arrow
        (Partite.Recursive.profile A D α) S C κ := by
  obtain ⟨Y, hY, O, hOPartite, hHalf⟩ :=
    Partite.SemiClosed.Picture.pictureLemma
      A D S α hSPartite hAtotal hDroot hSsingle κ
  letI : Finite Y := hY
  exact
    Partite.HalfClosed.inducedPartiteOver_singleton
      (Partite.Recursive.profile A D α) S O
      hpos.withFunctionDomains hSsingle hOPartite κ hHalf

/-- Process a finite list of ordinary A-to-D projections while preserving the
singleton-valued stage invariant. -/
theorem build
    (A : RelStructure L.withFunctionDomains.graph U)
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph P)
    [Finite U]
    (hpos : L.PositiveFuncArity)
    (hAtotal : A.FunctionDomainTotal)
    (hDroot : D.OutputImpliesDomain)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (S : Stage B D)
    (xs : List (RelStructure.Embedding A D)) :
    ∃ T : Stage B D,
      Partite.Recursive.CanonicalOn
        A D S.system T.system xs κ := by
  induction xs with
  | nil =>
      refine ⟨S, ?_⟩
      intro χ
      refine ⟨Partite.Closed.Embedding.id S.system, ?_⟩
      intro α hmem
      exact (List.not_mem_nil hmem).elim
  | cons α xs ih =>
      obtain ⟨T, hCanon⟩ := ih
      obtain ⟨Y, hY, C, hCPartite, hCSingle, hStep⟩ :=
        step A D hpos hAtotal hDroot κ
          T.system T.isPartite T.singleValued α
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hCPartite
        singleValued := hCSingle
      }
      refine ⟨R, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ :=
        hStep
          (fun e =>
            χ (Partite.Recursive.profileToRelClosed e))
      obtain ⟨f, hf⟩ :=
        hCanon
          (fun e =>
            χ (RelStructure.ClosedEmbedding.comp
              g.toRelClosed e))
      refine ⟨Partite.Closed.Embedding.comp g f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · have hlocal :=
          hg
            (Partite.Closed.Embedding.comp f e₁)
            (Partite.Closed.Embedding.comp f e₂)
        rw [Partite.Recursive.profileToRelClosed_comp,
          Partite.Recursive.profileToRelClosed_comp] at hlocal
        rw [Partite.Recursive.profile_comp_assoc,
          Partite.Recursive.profile_comp_assoc]
        exact hlocal
      · have hold := hf β hβ e₁ e₂
        rw [Partite.Recursive.profile_comp_assoc,
          Partite.Recursive.profile_comp_assoc]
        exact hold

/-- End-to-end recursive partite construction for the domain-expanded
partial-function setting. -/
theorem recursiveConstruction
    (A : RelStructure L.withFunctionDomains.graph U)
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (hAtotal : A.FunctionDomainTotal)
    (hDroot : D.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.withFunctionDomains.graph P X),
      C.FunctionOutputSingleValued ∧
      C.FunctionOutputTransversal ∧
      RelStructure.ClosedArrow
        A B C.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    Partite.Recursive.nonempty_embedding_of_arrow
      A B D κ hRamsey
  let S₀ := initialStage B D hpos hBsingle
  let xs := Partite.Recursive.allEmbeddings A D
  obtain ⟨T, hCanon⟩ :=
    build A B D hpos hAtotal hDroot κ S₀ xs
  refine
    ⟨T.Vertex, inferInstance, T.system,
      T.singleValued, T.singleValued.uTransversal, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hCanon χ
  let Liftable (α : RelStructure.Embedding A D) : Prop :=
    Nonempty
      (Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) S₀.system)
  let θ : RelStructure.Embedding A D → κ := fun α =>
    if hα : Liftable α then
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed
        (Partite.Recursive.profileToRelClosed
          (Classical.choice hα)))
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ
      (α : RelStructure.Embedding A D)
      (e : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) S₀.system) :
      θ α =
        χ (RelStructure.ClosedEmbedding.comp
          f.toRelClosed
          (Partite.Recursive.profileToRelClosed e)) := by
    have hLift : Liftable α := ⟨e⟩
    simp only [θ, dif_pos hLift]
    have hmem : α ∈ xs := by
      simp [xs]
    exact hf α hmem (Classical.choice hLift) e
  obtain ⟨β, hβ⟩ := hRamsey θ
  let j : RelStructure.ClosedEmbedding
      B S₀.system.toRelStructure :=
    Partite.HalfClosed.Initial.copyEmbedding
      B D hpos.withFunctionDomains β
  refine
    ⟨RelStructure.ClosedEmbedding.comp
      f.toRelClosed j, ?_⟩
  intro e₁ e₂
  let α₁ : RelStructure.Embedding A D :=
    β.comp e₁.toEmbedding
  let α₂ : RelStructure.Embedding A D :=
    β.comp e₂.toEmbedding
  let p₁ :
      Partite.Closed.Embedding
        (Partite.Recursive.profile A D α₁) S₀.system :=
    Partite.Recursive.initialProfileCopy
      A B D hpos.withFunctionDomains β e₁
  let p₂ :
      Partite.Closed.Embedding
        (Partite.Recursive.profile A D α₂) S₀.system :=
    Partite.Recursive.initialProfileCopy
      A B D hpos.withFunctionDomains β e₂
  have hmono := hβ e₁.toEmbedding e₂.toEmbedding
  rw [hθ α₁ p₁, hθ α₂ p₂] at hmono
  have hp₁ :
      Partite.Recursive.profileToRelClosed p₁ =
        RelStructure.ClosedEmbedding.comp j e₁ := by
    apply RelStructure.ClosedEmbedding.ext
    intro a
    rfl
  have hp₂ :
      Partite.Recursive.profileToRelClosed p₂ =
        RelStructure.ClosedEmbedding.comp j e₂ := by
    apply RelStructure.ClosedEmbedding.ext
    intro a
    rfl
  rw [hp₁, hp₂] at hmono
  exact hmono


/-- Starting from an arbitrary ordinary Ramsey witness in the relational
domain-expanded graph language, first root-prune it and then run the corrected
recursive construction.  Thus no root-compatibility assumption is needed on
the witness supplied by the ordinary relational Ramsey theorem. -/
theorem recursiveConstruction_from_ordinaryWitness
    (A₀ : Structure L U)
    (B₀ : Structure L V)
    (D : RelStructure L.withFunctionDomains.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (hAsingle : A₀.SingletonValued)
    (hBsingle : B₀.SingletonValued)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey :
      StructuralRamsey.Arrow
        A₀.withFunctionDomains.graph
        B₀.withFunctionDomains.graph
        D κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.withFunctionDomains.graph P X),
      C.FunctionOutputSingleValued ∧
      C.FunctionOutputTransversal ∧
      RelStructure.ClosedArrow
        A₀.withFunctionDomains.graph
        B₀.withFunctionDomains.graph
        C.toRelStructure κ := by
  let A := A₀.withFunctionDomains.graph
  let B := B₀.withFunctionDomains.graph
  let D' := RelStructure.rootPrune D
  have hAsemi := RelStructure.withFunctionDomains_graph_semiClosed A₀ hAsingle
  have hBsemi := RelStructure.withFunctionDomains_graph_semiClosed B₀ hBsingle
  have hAtotal :=
    RelStructure.withFunctionDomains_graph_domainTotal A₀
  have hDroot :=
    RelStructure.rootPrune_outputImpliesDomain D
  have hRamsey' :
      StructuralRamsey.Arrow A B D' κ :=
    RelStructure.arrow_rootPrune
      A B D hAsemi.1 hBsemi.1 κ hRamsey
  exact
    recursiveConstruction
      A B D' hpos hAtotal hDroot hBsemi.2 κ hRamsey'

end StructuralRamsey.Partite.SemiClosed.Recursive

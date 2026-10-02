import PartiteConstruction.Functional.ClosedPicture
import PartiteConstruction.Functional.ClosedInitial

/-! # End-to-end induced construction for set-valued functions

The direct full-language D-partite invariant is not preserved by free
attachment.  The correct functional construction is therefore carried out in
the relational graph encoding, using U-closed embeddings throughout.  For
positive-arity function symbols the initial disjoint union is U-transversal.
Every relevant U-closed A -> D copy is processed by the closed-alpha Picture
Lemma.  The final closed-arrow statement is equivalent to the original Ramsey
arrow for full embeddings.
-/
namespace StructuralRamsey.Partite.Closed.Construction

open RelStructure Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A relevant U-closed copy of A in D factors through a U-closed copy of B. -/
def Relevant
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (α : RelStructure.ClosedEmbedding A D) : Prop :=
  ∃ (β : RelStructure.ClosedEmbedding B D)
    (e : RelStructure.ClosedEmbedding A B),
    α = β.comp e

abbrev RelevantEmbedding
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P) :=
  {α : RelStructure.ClosedEmbedding A D // Relevant A B D α}

instance {A : RelStructure L.graph U}
    {B : RelStructure L.graph V} {D : RelStructure L.graph P}
    [Finite U] [Finite V] [Finite P] :
    Finite (RelevantEmbedding A B D) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- A stage of the functional induced construction. -/
structure Stage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : Partite.System L.graph P Vertex
  isPartite : system.IsPartiteOver D
  uTransversal : system.FunctionOutputTransversal

attribute [instance] Stage.finiteVertex

/-- A Ramsey arrow with a nonempty colour set yields a closed B -> D copy. -/
theorem nonempty_embedding_of_arrow
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (κ : Type*) [Nonempty κ]
    (h : RelStructure.ClosedArrow A B D κ) :
    Nonempty (RelStructure.ClosedEmbedding B D) := by
  classical
  let c : RelStructure.ClosedEmbedding A D → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨f, _⟩ := h c
  exact ⟨f⟩

/-- Initial stage: one indexed copy of B for every U-closed B -> D embedding. -/
def initialStage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    [Finite V] [Finite P]
    [Nonempty (RelStructure.ClosedEmbedding B D)] :
    Stage B D where
  Vertex := Partite.Closed.Initial.Index B D × V
  finiteVertex := inferInstance
  system := Partite.Closed.Initial.picture B D
  isPartite := Partite.Closed.Initial.isPartiteOver B D
  uTransversal := Partite.Closed.Initial.uTransversal B D hpos

/-- Canonicality of the current copy of an earlier stage for all processed
relevant projections. -/
def CanonicalOn
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    {X Y : Type v}
    (S : Partite.System L.graph P X)
    (T : Partite.System L.graph P Y)
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) : Prop :=
  ∀ χ : RelStructure.ClosedEmbedding A T.toRelStructure → κ,
    ∃ f : Partite.Closed.Embedding S T,
      ∀ α ∈ xs,
        ∀ e₁ e₂ : Partite.Closed.ProjectedEmbedding A S α.1,
          χ (Partite.Closed.ProjectedEmbedding.comp e₁ f).1 =
            χ (Partite.Closed.ProjectedEmbedding.comp e₂ f).1

/-- Process a finite list of relevant closed projections. -/
theorem build
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (S : Stage B D)
    [Finite U]
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) [Fintype κ] :
    ∃ T : Stage B D,
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
      obtain ⟨Y, hY, C, hPartite, hU, hPicture⟩ :=
        Partite.Closed.Picture.pictureLemma
          (A := A) (D := D) (B := T.system) (α := α.1)
          T.isPartite T.uTransversal κ
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hPartite
        uTransversal := hU
      }
      refine ⟨R, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hPicture (fun e => χ e.1)
      obtain ⟨f, hf⟩ := hT
        (fun e => χ (RelStructure.ClosedEmbedding.comp g.toRelClosed e))
      refine ⟨Partite.Closed.Embedding.comp g f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg
          (Partite.Closed.ProjectedEmbedding.comp e₁ f)
          (Partite.Closed.ProjectedEmbedding.comp e₂ f)
      · exact hf β hβ e₁ e₂

/-- List all relevant closed embeddings. -/
noncomputable def allRelevant
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P] :
    List (RelevantEmbedding A B D) := by
  classical
  letI : Fintype (RelevantEmbedding A B D) := Fintype.ofFinite _
  exact Finset.univ.toList

@[simp] theorem mem_allRelevant
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (α : RelevantEmbedding A B D) :
    α ∈ allRelevant A B D := by
  classical
  letI : Fintype (RelevantEmbedding A B D) := Fintype.ofFinite _
  simp [allRelevant]

/-- The initial closed A-copy inside the copy indexed by beta. -/
def initialProjectedCopy
    (hpos : L.PositiveFuncArity)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (β : RelStructure.ClosedEmbedding B D)
    (e : RelStructure.ClosedEmbedding A B) :
    Partite.Closed.ProjectedEmbedding A
      (Partite.Closed.Initial.picture B D)
      (β.comp e) := by
  let j := Partite.Closed.Initial.copyEmbedding B D hpos β
  refine ⟨RelStructure.ClosedEmbedding.comp j e, ?_⟩
  intro x
  rfl

/-- Corrected end-to-end induced construction for set-valued functions.
It works in the graph encoding and with U-closed embeddings. -/
theorem inducedConstruction
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.ClosedArrow A B D κ) :
    letI : Nonempty (RelStructure.ClosedEmbedding B D) :=
      nonempty_embedding_of_arrow A B D κ hRamsey
    let S₀ := initialStage B D hpos
    ∃ T : Stage B D,
      RelStructure.ClosedArrow A B T.system.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.ClosedEmbedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D hpos
  let xs := allRelevant A B D
  obtain ⟨T, hCanon⟩ := build A B D S₀ xs κ
  refine ⟨T, ?_⟩
  intro χ
  let projected
      (α : RelStructure.ClosedEmbedding A D)
      (hα : Relevant A B D α) :
      Partite.Closed.ProjectedEmbedding A S₀.system α := by
    let β : RelStructure.ClosedEmbedding B D := Classical.choose hα
    have hrest :
        ∃ e : RelStructure.ClosedEmbedding A B, α = β.comp e :=
      Classical.choose_spec hα
    let e : RelStructure.ClosedEmbedding A B := Classical.choose hrest
    have hfac : α = β.comp e := Classical.choose_spec hrest
    rw [hfac]
    exact initialProjectedCopy hpos B D β e
  -- Obtain the canonical copy first; define the induced colouring using it.
  obtain ⟨f, hf⟩ := hCanon χ
  let θ' : RelStructure.ClosedEmbedding A D → κ := fun α =>
    if hα : Relevant A B D α then
      χ (RelStructure.ClosedEmbedding.comp f.toRelClosed (projected α hα).1)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, hβ⟩ := hRamsey θ'
  let j := Partite.Closed.Initial.copyEmbedding B D hpos β
  refine ⟨RelStructure.ClosedEmbedding.comp f.toRelClosed j, ?_⟩
  intro e₁ e₂
  let α₁ := β.comp e₁
  let α₂ := β.comp e₂
  have hα₁ : Relevant A B D α₁ := ⟨β, e₁, rfl⟩
  have hα₂ : Relevant A B D α₂ := ⟨β, e₂, rfl⟩
  have hm₁ :
      (⟨α₁, hα₁⟩ : RelevantEmbedding A B D) ∈ xs := by
    simp [xs]
  have hm₂ :
      (⟨α₂, hα₂⟩ : RelevantEmbedding A B D) ∈ xs := by
    simp [xs]
  have hcanon :=
    hf
      ⟨α₁, hα₁⟩ hm₁
      (initialProjectedCopy hpos B D β e₁)
      (projected α₁ hα₁)
  have hcanon₂ :=
    hf
      ⟨α₂, hα₂⟩ hm₂
      (initialProjectedCopy hpos B D β e₂)
      (projected α₂ hα₂)
  have hmono0 := hβ e₁ e₂
  have hmono :
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (projected α₁ hα₁).1) =
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (projected α₂ hα₂).1) := by
    simpa [θ', α₁, α₂, hα₁, hα₂] using hmono0
  have hinit :
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (initialProjectedCopy hpos B D β e₁).1) =
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (initialProjectedCopy hpos B D β e₂).1) := by
    exact hcanon.trans (hmono.trans hcanon₂.symm)
  have hj₁ :
      (initialProjectedCopy hpos B D β e₁).1 =
        RelStructure.ClosedEmbedding.comp j e₁ := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hj₂ :
      (initialProjectedCopy hpos B D β e₂).1 =
        RelStructure.ClosedEmbedding.comp j e₂ := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hassoc₁ :
      RelStructure.ClosedEmbedding.comp
          (RelStructure.ClosedEmbedding.comp f.toRelClosed j) e₁ =
        RelStructure.ClosedEmbedding.comp
          f.toRelClosed (RelStructure.ClosedEmbedding.comp j e₁) := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  have hassoc₂ :
      RelStructure.ClosedEmbedding.comp
          (RelStructure.ClosedEmbedding.comp f.toRelClosed j) e₂ =
        RelStructure.ClosedEmbedding.comp
          f.toRelClosed (RelStructure.ClosedEmbedding.comp j e₂) := by
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl
  rw [hassoc₁, hassoc₂, ← hj₁, ← hj₂]
  exact hinit

end StructuralRamsey.Partite.Closed.Construction

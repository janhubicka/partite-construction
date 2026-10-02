import PartiteConstruction.Functional.HalfClosedInitial
import PartiteConstruction.Functional.ClosedPicture

/-! # Half-closed induced partite construction

This formalizes the survey's "half U-closed" partite construction.  The input
Ramsey hypothesis colours U-closed A-copies in D and may return an ordinary
embedding B -> D; only the composites with U-closed A -> B copies are required
to be U-closed and monochromatic.

The output repairs this defect: it is a U-transversal D-partite system with a
genuine closed Ramsey arrow.
-/
namespace StructuralRamsey.RelStructure

open Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Half-closed Ramsey arrow.  The ordinary embedding beta need not be closed.
The map `lift e` packages the assertion that beta composed with the closed
copy e is itself closed. -/
def HalfClosedArrow
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (κ : Type*) : Prop :=
  ∀ χ : ClosedEmbedding A D → κ,
    ∃ β : Embedding B D,
      ∃ lift : ClosedEmbedding A B → ClosedEmbedding A D,
        (∀ e x, lift e x = β (e x)) ∧
        ∀ e₁ e₂, χ (lift e₁) = χ (lift e₂)

/-- A half-closed arrow with a nonempty colour type contains an ordinary
B-copy. -/
theorem nonempty_embedding_of_halfClosedArrow
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (κ : Type*) [Nonempty κ]
    (h : HalfClosedArrow A B D κ) :
    Nonempty (Embedding B D) := by
  classical
  let χ : ClosedEmbedding A D → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, _⟩ := h χ
  exact ⟨β⟩

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Partite.HalfClosed.Construction

open RelStructure Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- A closed A-copy in D is relevant if its underlying map factors through an
ordinary B-copy using a closed A-copy of B. -/
def Relevant
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (α : RelStructure.ClosedEmbedding A D) : Prop :=
  ∃ (β : RelStructure.Embedding B D)
    (e : RelStructure.ClosedEmbedding A B),
    ∀ x, α x = β (e x)

/-- For a closed alpha, factorization through an ordinary B-copy is
equivalent to the survey's image-containment formulation.  Closedness of alpha
forces the induced A -> B factor to be closed even when beta itself is not. -/
theorem relevant_iff_image_contained
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (α : RelStructure.ClosedEmbedding A D) :
    Relevant A B D α ↔
      ∃ β : RelStructure.Embedding B D,
        ∀ a : U, ∃ b : V, α a = β b := by
  constructor
  · rintro ⟨β, e, hfac⟩
    exact ⟨β, fun a => ⟨e a, hfac a⟩⟩
  · rintro ⟨β, hβ⟩
    choose q hq using hβ
    have hinj : Function.Injective q := by
      intro x y hxy
      apply α.toEmbedding.injective
      rw [hq x, hq y, hxy]
    let e0 : RelStructure.Embedding A B := {
      toFun := q
      injective := hinj
      map_rel_iff := by
        intro R x
        have hfun : α.toEmbedding ∘ x = β ∘ (q ∘ x) := by
          funext i
          exact hq (x i)
        have hα := α.toEmbedding.map_rel_iff R x
        have hβmap := β.map_rel_iff R (q ∘ x)
        rw [← hα, hfun]
        exact hβmap.symm
    }
    have hclosed : RelStructure.FunctionClosedMap A B q := by
      intro F x y hy
      have hyD0 :
          D.rel (.inr F)
            (β ∘ Structure.funcTuple (q ∘ x) y) :=
        (β.map_rel_iff (.inr F)
          (Structure.funcTuple (q ∘ x) y)).mpr hy
      have htuple :
          β ∘ Structure.funcTuple (q ∘ x) y =
            Structure.funcTuple (α ∘ x) (β y) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Structure.funcTuple, Function.comp_apply]
        · simp [Structure.funcTuple, Function.comp_apply, hq]
      have hyD :
          D.rel (.inr F)
            (Structure.funcTuple (α ∘ x) (β y)) := by
        rw [← htuple]
        exact hyD0
      obtain ⟨z, hz, hzy⟩ := α.closed F x (β y) hyD
      refine ⟨z, hz, ?_⟩
      apply β.injective
      calc
        β (q z) = α z := (hq z).symm
        _ = β y := hzy
    let e : RelStructure.ClosedEmbedding A B := ⟨e0, hclosed⟩
    exact ⟨β, e, fun x => hq x⟩

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

/-- A stage repaired to be U-transversal, while its projection to D remains
only a relational homomorphism-embedding. -/
structure Stage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : Partite.System L.graph P Vertex
  isPartite : system.IsPartiteOver D
  uTransversal : system.FunctionOutputTransversal

attribute [instance] Stage.finiteVertex

/-- Initial stage indexed by all ordinary B -> D copies.  Each actual copy
inside the disjoint union is closed. -/
def initialStage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    [Finite V] [Finite P]
    [Nonempty (RelStructure.Embedding B D)] :
    Stage B D where
  Vertex := Partite.HalfClosed.Initial.Index B D × V
  finiteVertex := inferInstance
  system := Partite.HalfClosed.Initial.picture B D
  isPartite := Partite.HalfClosed.Initial.isPartiteOver B D
  uTransversal := Partite.HalfClosed.Initial.uTransversal B D hpos

/-- Canonicality on a finite family of relevant closed projections. -/
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
          χ (RelStructure.ClosedEmbedding.comp f.toRelClosed e₁.1) =
            χ (RelStructure.ClosedEmbedding.comp f.toRelClosed e₂.1)

/-- Process a finite list of relevant closed projections using only the valid
closed-alpha Picture Lemma. -/
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

/-- The initial closed A-copy inside the ordinary copy indexed by beta. -/
def initialProjectedCopy
    (hpos : L.PositiveFuncArity)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (α : RelStructure.ClosedEmbedding A D)
    (β : RelStructure.Embedding B D)
    (e : RelStructure.ClosedEmbedding A B)
    (hfac : ∀ x, α x = β (e x)) :
    Partite.Closed.ProjectedEmbedding A
      (Partite.HalfClosed.Initial.picture B D) α := by
  let j := Partite.HalfClosed.Initial.copyEmbedding B D hpos β
  refine ⟨RelStructure.ClosedEmbedding.comp j e, ?_⟩
  intro x
  change β (e x) = α x
  exact (hfac x).symm

/-- Corrected half-closed induced partite construction.  Ordinary B-copies in
D are sufficient initially; after the construction the selected B-copy in the
output is genuinely U-closed. -/
theorem inducedConstruction
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.HalfClosedArrow A B D κ) :
    letI : Nonempty (RelStructure.Embedding B D) :=
      RelStructure.nonempty_embedding_of_halfClosedArrow A B D κ hRamsey
    let S₀ := initialStage B D hpos
    ∃ T : Stage B D,
      RelStructure.ClosedArrow A B T.system.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    RelStructure.nonempty_embedding_of_halfClosedArrow A B D κ hRamsey
  let S₀ := initialStage B D hpos
  let xs := allRelevant A B D
  obtain ⟨T, hCanon⟩ := build A B D S₀ xs κ
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
    let e : RelStructure.ClosedEmbedding A B := Classical.choose hrest
    have hfac : ∀ x, α x = β (e x) := Classical.choose_spec hrest
    exact initialProjectedCopy hpos B D α β e hfac
  obtain ⟨f, hf⟩ := hCanon χ
  let θ : RelStructure.ClosedEmbedding A D → κ := fun α =>
    if hα : Relevant A B D α then
      χ (RelStructure.ClosedEmbedding.comp f.toRelClosed (projected α hα).1)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, lift, hlift, hmono⟩ := hRamsey θ
  let j : RelStructure.ClosedEmbedding B S₀.system.toRelStructure :=
    Partite.HalfClosed.Initial.copyEmbedding B D hpos β
  refine ⟨RelStructure.ClosedEmbedding.comp f.toRelClosed j, ?_⟩
  intro e₁ e₂
  let α₁ : RelStructure.ClosedEmbedding A D := lift e₁
  let α₂ : RelStructure.ClosedEmbedding A D := lift e₂
  have hα₁ : Relevant A B D α₁ := ⟨β, e₁, hlift e₁⟩
  have hα₂ : Relevant A B D α₂ := ⟨β, e₂, hlift e₂⟩
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
      χ (RelStructure.ClosedEmbedding.comp f.toRelClosed p₁.1) =
        χ (RelStructure.ClosedEmbedding.comp f.toRelClosed p₂.1) := by
    exact hc₁.trans (ht₁.symm.trans ((hmono e₁ e₂).trans (ht₂.trans hc₂.symm)))
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
  rw [hassoc₁, hassoc₂, ← hp₁, ← hp₂]
  exact hpmono

end StructuralRamsey.Partite.HalfClosed.Construction

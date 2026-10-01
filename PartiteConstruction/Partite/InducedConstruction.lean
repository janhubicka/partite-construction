import PartiteConstruction.Partite.InducedStep
import PartiteConstruction.Partite.Construction

/-! # Finite induced partite construction

The construction processes exactly the embeddings of `A` into `D` that
factor through a copy of `B`.  A heterogeneous trace records every stage:
each stage is finite, remains `D`-partite, satisfies the irreducible-image
invariant, and every transition is formally `BasedOn` the preceding stage.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- A finite picture carrying both invariants of the induced construction. -/
structure Stage (B : RelStructure L V) (D : RelStructure L P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : System L P Vertex
  isPartite : system.IsPartiteOver D
  covers : system.CoversIrreduciblesBy B D

attribute [instance] Stage.finiteVertex

/-- The initial stage is the disjoint union of one copy of `B` for every
embedding of `B` into `D`. -/
def initialStage (B : RelStructure L V) (D : RelStructure L P)
    [Finite V] [Finite P] [Nonempty (RelStructure.Embedding B D)] :
    Stage B D where
  Vertex := RelStructure.Embedding B D × V
  finiteVertex := inferInstance
  system := Partite.Initial.picture B
    (fun β : RelStructure.Embedding B D => β.toFunctionEmbedding)
  isPartite := Initial.picture_isPartiteOver D
    (fun β : RelStructure.Embedding B D => β)
  covers := Initial.picture_covers D
    (fun β : RelStructure.Embedding B D => β)

/-- Every node of the trace is already a stage satisfying invariant (3);
each transition additionally records that the new picture is based on the
preceding one over the indicated relevant embedding. -/
inductive Trace
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P) :
    Stage B D → List (RelevantEmbedding A B D) → Stage B D → Prop
  | nil (S : Stage B D) : Trace A B D S [] S
  | snoc {S T R : Stage B D} {xs : List (RelevantEmbedding A B D)}
      (h : Trace A B D S xs T) (α : RelevantEmbedding A B D)
      (hBased : R.system.BasedOn A D T.system α.1) :
      Trace A B D S (xs ++ [α]) R

/-- The list of partition projections corresponding to a list of relevant
embeddings. -/
def projectionProfiles
    (xs : List (RelevantEmbedding A B D)) : List (U ↪ P) :=
  xs.map (fun α => α.1.toFunctionEmbedding)

/-- Build all requested stages.  The trace runs in the reverse of the input
list because the witness object is assembled by the same backwards induction
used in the non-induced construction; the order is immaterial once all
relevant embeddings are listed. -/
theorem build
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (S : Stage B D) [Finite U]
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) [Fintype κ] :
    ∃ T : Stage B D,
      Trace A B D S xs.reverse T ∧
      CanonicalOn A S.system T.system (projectionProfiles A B D xs) κ := by
  induction xs with
  | nil =>
      refine ⟨S, Trace.nil S, ?_⟩
      intro χ
      exact ⟨Partite.Embedding.id S.system,
        fun α h => (List.not_mem_nil h).elim⟩
  | cons α xs ih =>
      obtain ⟨T, hTrace, hCanon⟩ := ih
      obtain ⟨Y, hY, C, hPartite, hCover, hBased, hPicture⟩ :=
        pictureStep A B D T.system α κ T.isPartite T.covers
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hPartite
        covers := hCover
      }
      refine ⟨R, ?_, ?_⟩
      · simpa [List.reverse_cons] using
          Trace.snoc hTrace α hBased
      · intro χ
        obtain ⟨g, hg⟩ := hPicture (fun e => χ e.val)
        obtain ⟨f, hf⟩ := hCanon
          (fun e => χ (g.toEmbedding.comp e))
        refine ⟨g.comp f, ?_⟩
        intro β hβ e₁ e₂
        simp only [projectionProfiles, List.map_cons, List.mem_cons] at hβ
        rcases hβ with rfl | hβ
        · exact hg (e₁.comp f) (e₂.comp f)
        · exact hf β hβ e₁ e₂

/-- A Ramsey arrow with a nonempty colour type forces at least one copy of
the target structure. -/
theorem nonempty_embedding_of_arrow
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (κ : Type*) [Nonempty κ]
    (h : StructuralRamsey.Arrow A B D κ) :
    Nonempty (RelStructure.Embedding B D) := by
  classical
  let c : RelStructure.Embedding A D → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨f, _⟩ := h c
  exact ⟨f⟩

/-- The initial copy indexed by `β : B ↪ D`, with an `A`-copy inside it,
has projection `β ∘ e`. -/
def initialProjectedCopy
    (B : RelStructure L V) (D : RelStructure L P)
    (β : RelStructure.Embedding B D) (e : RelStructure.Embedding A B) :
    ProjectedEmbedding A
      (Partite.Initial.picture B
        (fun γ : RelStructure.Embedding B D => γ.toFunctionEmbedding))
      (β.comp e).toFunctionEmbedding :=
  ⟨(Partite.Initial.copyEmbedding B
      (fun γ : RelStructure.Embedding B D => γ.toFunctionEmbedding) β).comp e,
    fun _ => rfl⟩

/-- End-to-end induced partite construction, including the Ramsey extraction.
The returned trace verifies the initial/disjoint-copy stage, every based
transition, and invariant (3) at every intermediate stage. -/
theorem inducedConstruction
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ) :
    letI : Nonempty (RelStructure.Embedding B D) :=
      nonempty_embedding_of_arrow A B D κ hRamsey
    let S₀ := initialStage B D
    ∃ T : Stage B D,
      Trace A B D S₀
        (Finset.univ.toList :
          List (RelevantEmbedding A B D)).reverse T ∧
      StructuralRamsey.Arrow A B T.system.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D
  letI : Fintype (RelevantEmbedding A B D) := Fintype.ofFinite _
  let xs : List (RelevantEmbedding A B D) := Finset.univ.toList
  obtain ⟨T, hTrace, hCanon⟩ := build A B D S₀ xs κ
  refine ⟨T, hTrace, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hCanon χ
  let P₀ := S₀.system
  let projected (α : RelStructure.Embedding A D)
      (hα : Relevant A B D α) :
      ProjectedEmbedding A P₀ α.toFunctionEmbedding := by
    rcases hα with ⟨β, e, hfac⟩
    refine ⟨(Partite.Initial.copyEmbedding B
      (fun γ : RelStructure.Embedding B D => γ.toFunctionEmbedding) β).comp e, ?_⟩
    intro x
    change β (e x) = α x
    rw [hfac]
    rfl
  let θ : RelStructure.Embedding A D → κ := fun α =>
    if hα : Relevant A B D α then
      χ (f.toEmbedding.comp (projected α hα).val)
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ (α : RelStructure.Embedding A D)
      (hα : Relevant A B D α)
      (e : ProjectedEmbedding A P₀ α.toFunctionEmbedding) :
      θ α = χ (f.toEmbedding.comp e.val) := by
    simp only [θ, dite_eq_left hα]
    let r : RelevantEmbedding A B D := ⟨α, hα⟩
    have hr : r ∈ xs := by
      simp [xs]
    have hp : α.toFunctionEmbedding ∈ projectionProfiles A B D xs := by
      exact List.mem_map.mpr ⟨r, hr, rfl⟩
    exact hf α.toFunctionEmbedding hp (projected α hα) e
  obtain ⟨β, hβ⟩ := hRamsey θ
  let j : RelStructure.Embedding B P₀.toRelStructure :=
    Partite.Initial.copyEmbedding B
      (fun γ : RelStructure.Embedding B D => γ.toFunctionEmbedding) β
  refine ⟨f.toEmbedding.comp j, ?_⟩
  intro e₁ e₂
  let α₁ := β.comp e₁
  let α₂ := β.comp e₂
  have hα₁ : Relevant A B D α₁ := ⟨β, e₁, rfl⟩
  have hα₂ : Relevant A B D α₂ := ⟨β, e₂, rfl⟩
  have h := hβ e₁ e₂
  rw [hθ α₁ hα₁ (initialProjectedCopy (A := A) B D β e₁),
      hθ α₂ hα₂ (initialProjectedCopy (A := A) B D β e₂)] at h
  simpa only [j, RelStructure.Embedding.comp_assoc] using h

end StructuralRamsey.Partite.Induced

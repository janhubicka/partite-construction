import PartiteConstruction.Functional.HalfClosedPartite
import PartiteConstruction.Functional.HalfClosedInitial
import PartiteConstruction.Ramsey.Basic

/-! # Outer recursive partite iteration

This is the finite outer recursion in the proof of the U-closed Ramsey theorem.

The local input is isolated explicitly: for each ordinary projection alpha from
A to D and each current U-transversal D-partite picture S, one needs a finite
U-transversal picture O with the half-closed Ramsey property for alpha.  The
already verified native half-closed construction turns such an O into a new
U-transversal stage with a genuine closed arrow.

This file proves that these local witnesses are the only missing Ramsey input:
processing all ordinary A-to-D projections and then applying the ordinary
Ramsey arrow D -> (B)^A yields a final U-closed Ramsey arrow.
-/
namespace StructuralRamsey.Partite.Recursive

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {U V P : Type v}


@[simp] theorem toRelClosed_comp
    {Q : Type v}
    {A : Partite.System L.graph P U}
    {B : Partite.System L.graph P V}
    {C : Partite.System L.graph P Q}
    (g : Partite.Closed.Embedding B C)
    (f : Partite.Closed.Embedding A B) :
    (Partite.Closed.Embedding.comp g f).toRelClosed =
      RelStructure.ClosedEmbedding.comp g.toRelClosed f.toRelClosed := by
  apply RelStructure.ClosedEmbedding.ext
  intro x
  rfl

theorem relClosed_comp_assoc
    {Q : Type v}
    {A : RelStructure L.graph U}
    {B : RelStructure L.graph V}
    {C : RelStructure L.graph P}
    {E : RelStructure L.graph Q}
    (h : RelStructure.ClosedEmbedding C E)
    (g : RelStructure.ClosedEmbedding B C)
    (f : RelStructure.ClosedEmbedding A B) :
    RelStructure.ClosedEmbedding.comp
        (RelStructure.ClosedEmbedding.comp h g) f =
      RelStructure.ClosedEmbedding.comp h
        (RelStructure.ClosedEmbedding.comp g f) := by
  apply RelStructure.ClosedEmbedding.ext
  intro x
  rfl

/-- The D-partite source system corresponding to one ordinary projection. -/
def profile
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (α : RelStructure.Embedding A D) :
    Partite.System L.graph P U :=
  Partite.withProjection A α.toFunctionEmbedding

/-- Forget the part labels on a closed profile embedding, normalizing its
source definitionally to A. -/
def profileToRelClosed
    {X : Type v}
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    {α : RelStructure.Embedding A D}
    {S : Partite.System L.graph P X}
    (e : Partite.Closed.Embedding (profile A D α) S) :
    RelStructure.ClosedEmbedding A S.toRelStructure := by
  exact e.toRelClosed

theorem profileToRelClosed_comp
    {X Y : Type v}
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    {α : RelStructure.Embedding A D}
    {S : Partite.System L.graph P X}
    {T : Partite.System L.graph P Y}
    (f : Partite.Closed.Embedding S T)
    (e : Partite.Closed.Embedding (profile A D α) S) :
    profileToRelClosed (Partite.Closed.Embedding.comp f e) =
      RelStructure.ClosedEmbedding.comp f.toRelClosed
        (profileToRelClosed e) := by
  apply RelStructure.ClosedEmbedding.ext
  intro x
  rfl

theorem profile_comp_assoc
    {X Y Z : Type v}
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    {α : RelStructure.Embedding A D}
    {S : Partite.System L.graph P X}
    {T : Partite.System L.graph P Y}
    {C : Partite.System L.graph P Z}
    (g : Partite.Closed.Embedding T C)
    (f : Partite.Closed.Embedding S T)
    (e : Partite.Closed.Embedding (profile A D α) S) :
    RelStructure.ClosedEmbedding.comp
        (Partite.Closed.Embedding.comp g f).toRelClosed
        (profileToRelClosed e) =
      RelStructure.ClosedEmbedding.comp g.toRelClosed
        (RelStructure.ClosedEmbedding.comp f.toRelClosed
          (profileToRelClosed e)) := by
  apply RelStructure.ClosedEmbedding.ext
  intro x
  rfl

/-- One finite stage of the outer recursive construction. -/
structure Stage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : Partite.System L.graph P Vertex
  uTransversal : system.FunctionOutputTransversal

attribute [instance] Stage.finiteVertex

/-- Initial stage: a disjoint U-closed copy of B for every ordinary B-to-D
embedding. -/
def initialStage
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    [Nonempty (RelStructure.Embedding B D)] :
    Stage B D where
  Vertex := Partite.HalfClosed.Initial.Index B D × V
  finiteVertex := inferInstance
  system := Partite.HalfClosed.Initial.picture B D
  uTransversal := Partite.HalfClosed.Initial.uTransversal B D hpos

/-- Canonicality of one embedded copy of an earlier stage for a finite list of
ordinary projections. -/
def CanonicalOn
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    {X Y : Type v}
    (S : Partite.System L.graph P X)
    (T : Partite.System L.graph P Y)
    (profiles : List (RelStructure.Embedding A D))
    (κ : Type*) : Prop :=
  ∀ χ : RelStructure.ClosedEmbedding A T.toRelStructure → κ,
    ∃ f : Partite.Closed.Embedding S T,
      ∀ α ∈ profiles,
        ∀ e₁ e₂ :
            Partite.Closed.Embedding (profile A D α) S,
          χ (RelStructure.ClosedEmbedding.comp
            f.toRelClosed (profileToRelClosed e₁)) =
          χ (RelStructure.ClosedEmbedding.comp
            f.toRelClosed (profileToRelClosed e₂))


/-- Closed embeddings of a profile system are exactly closed embeddings of A
with that prescribed projection. -/
def profileEmbeddingToProjected
    {X : Type v}
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    {α : RelStructure.Embedding A D}
    {S : Partite.System L.graph P X}
    (e : Partite.Closed.Embedding (profile A D α) S) :
    Partite.Closed.ProjectedEmbedding A S α :=
  ⟨profileToRelClosed e, e.1.map_part⟩

/-- The inverse conversion from a closed projected A-copy to a closed
embedding of the profile system. -/
def projectedToProfileEmbedding
    {X : Type v}
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    {α : RelStructure.Embedding A D}
    {S : Partite.System L.graph P X}
    (e : Partite.Closed.ProjectedEmbedding A S α) :
    Partite.Closed.Embedding (profile A D α) S := by
  let pe : Partite.Embedding (profile A D α) S := {
    toEmbedding := e.1.toEmbedding
    map_part := e.2
  }
  exact ⟨pe, e.1.closed⟩

/-- For an already U-closed projection alpha, the checked closed-alpha Picture
lemma supplies exactly the local half-closed witness needed by the outer
recursion.  Hence the unresolved local existence problem concerns only
non-closed ordinary projections. -/
theorem localHalfClosedPicture_of_closed
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    [Finite U]
    {X : Type v} [Finite X]
    (S : Partite.System L.graph P X)
    (hSPartite : S.IsPartiteOver D)
    (hSU : S.FunctionOutputTransversal)
    (κ : Type*) [Fintype κ]
    (α : RelStructure.ClosedEmbedding A D) :
    ∃ (Y : Type v) (_ : Finite Y)
      (O : Partite.System L.graph P Y),
      O.FunctionOutputTransversal ∧
      Partite.HalfClosedArrow
        (A := profile A D α.toEmbedding)
        (B := S) (D := O) κ := by
  obtain ⟨Y, hY, O, hOPartite, hOU, hPicture⟩ :=
    Partite.Closed.Picture.pictureLemma
      (A := A) (D := D) (B := S) (α := α)
      hSPartite hSU κ
  refine ⟨Y, hY, O, hOU, ?_⟩
  intro χ
  let χ' : Partite.Closed.ProjectedEmbedding A O α → κ :=
    fun e => χ (projectedToProfileEmbedding
      (D := D) (α := α.toEmbedding) e)
  obtain ⟨f, hf⟩ := hPicture χ'
  let lift :
      Partite.Closed.Embedding
          (profile A D α.toEmbedding) S →
        Partite.Closed.Embedding
          (profile A D α.toEmbedding) O :=
    fun e => Partite.Closed.Embedding.comp f e
  refine ⟨f.1, lift, ?_, ?_⟩
  · intro e x
    rfl
  · intro e₁ e₂
    have h :=
      hf
        (profileEmbeddingToProjected
          (D := D) (α := α.toEmbedding) e₁)
        (profileEmbeddingToProjected
          (D := D) (α := α.toEmbedding) e₂)
    exact h

/-- The exact local existence statement still required from the
arbitrary-projection Picture step. -/
def LocalHalfClosedPictures
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (κ : Type*) : Prop :=
  ∀ {X : Type v} (_ : Finite X)
    (S : Partite.System L.graph P X),
    S.FunctionOutputTransversal →
    ∀ α : RelStructure.Embedding A D,
      ∃ (Y : Type v) (_ : Finite Y)
        (O : Partite.System L.graph P Y),
        O.FunctionOutputTransversal ∧
        Partite.HalfClosedArrow
          (A := profile A D α) (B := S) (D := O) κ

/-- The local half-closed Picture input plus the checked native rpartite
construction gives one genuine closed-arrow recursive step. -/
theorem step_of_localPictures
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    [Finite U]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hLocal : LocalHalfClosedPictures A D κ)
    {X : Type v} [Finite X]
    (S : Partite.System L.graph P X)
    (hS : S.FunctionOutputTransversal)
    (α : RelStructure.Embedding A D) :
    ∃ (Y : Type v) (_ : Finite Y)
      (C : Partite.System L.graph P Y),
      C.FunctionOutputTransversal ∧
      Partite.Closed.Arrow (profile A D α) S C κ := by
  obtain ⟨Y, hY, O, hOU, hHalf⟩ :=
    hLocal (inferInstance : Finite X) S hS α
  letI : Finite Y := hY
  exact Partite.HalfClosed.inducedPartite
    (profile A D α) S O hpos hOU κ hHalf

/-- Process a finite list of ordinary projections. -/
theorem build
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hLocal : LocalHalfClosedPictures A D κ)
    (S : Stage B D)
    (xs : List (RelStructure.Embedding A D)) :
    ∃ T : Stage B D,
      CanonicalOn A D S.system T.system xs κ := by
  induction xs with
  | nil =>
      refine ⟨S, ?_⟩
      intro χ
      refine ⟨Partite.Closed.Embedding.id S.system, ?_⟩
      intro α hmem
      exact (List.not_mem_nil hmem).elim
  | cons α xs ih =>
      obtain ⟨T, hCanon⟩ := ih
      obtain ⟨Y, hY, C, hCU, hStep⟩ :=
        step_of_localPictures
          A D hpos κ hLocal T.system T.uTransversal α
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        uTransversal := hCU
      }
      refine ⟨R, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ :=
        hStep (fun e => χ (profileToRelClosed e))
      obtain ⟨f, hf⟩ :=
        hCanon
          (fun e =>
            χ (RelStructure.ClosedEmbedding.comp g.toRelClosed e))
      refine ⟨Partite.Closed.Embedding.comp g f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · have hlocal :=
          hg
            (Partite.Closed.Embedding.comp f e₁)
            (Partite.Closed.Embedding.comp f e₂)
        rw [profileToRelClosed_comp, profileToRelClosed_comp] at hlocal
        rw [profile_comp_assoc, profile_comp_assoc]
        exact hlocal
      · have hold := hf β hβ e₁ e₂
        rw [profile_comp_assoc, profile_comp_assoc]
        exact hold

/-- Enumerate every ordinary A-copy in D. -/
noncomputable def allEmbeddings
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    [Finite U] [Finite P] :
    List (RelStructure.Embedding A D) := by
  classical
  letI : Fintype (RelStructure.Embedding A D) := Fintype.ofFinite _
  exact Finset.univ.toList

@[simp] theorem mem_allEmbeddings
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    [Finite U] [Finite P]
    (α : RelStructure.Embedding A D) :
    α ∈ allEmbeddings A D := by
  classical
  letI : Fintype (RelStructure.Embedding A D) := Fintype.ofFinite _
  simp [allEmbeddings]

/-- A closed A-copy inside the initial copy indexed by beta has the expected
ordinary projection beta composed with e. -/
def initialProfileCopy
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    (β : RelStructure.Embedding B D)
    (e : RelStructure.ClosedEmbedding A B) :
    Partite.Closed.Embedding
      (profile A D (β.comp e.toEmbedding))
      (Partite.HalfClosed.Initial.picture B D) := by
  let j := Partite.HalfClosed.Initial.copyEmbedding B D hpos β
  let ce : RelStructure.ClosedEmbedding A
      (Partite.HalfClosed.Initial.picture B D).toRelStructure :=
    RelStructure.ClosedEmbedding.comp j e
  let pe : Partite.Embedding
      (profile A D (β.comp e.toEmbedding))
      (Partite.HalfClosed.Initial.picture B D) := {
    toEmbedding := ce.toEmbedding
    map_part := by
      intro a
      rfl
  }
  exact ⟨pe, ce.closed⟩

@[simp] theorem initialProfileCopy_toRelClosed_apply
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    (β : RelStructure.Embedding B D)
    (e : RelStructure.ClosedEmbedding A B)
    (a : U) :
    (initialProfileCopy A B D hpos β e).toRelClosed a =
      (Partite.HalfClosed.Initial.copyEmbedding B D hpos β) (e a) :=
  rfl

/-- An ordinary Ramsey arrow contains at least one ordinary B-copy. -/
theorem nonempty_embedding_of_arrow
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (κ : Type*) [Nonempty κ]
    (h : StructuralRamsey.Arrow A B D κ) :
    Nonempty (RelStructure.Embedding B D) := by
  classical
  let χ : RelStructure.Embedding A D → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, _⟩ := h χ
  exact ⟨β⟩

/-- End-to-end outer recursive iteration, conditional only on the local
arbitrary-projection half-closed Picture witnesses. -/
theorem recursiveConstruction_of_localPictures
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ)
    (hLocal : LocalHalfClosedPictures A D κ) :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.FunctionOutputTransversal ∧
      RelStructure.ClosedArrow A B C.toRelStructure κ := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D hpos
  let xs := allEmbeddings A D
  obtain ⟨T, hCanon⟩ :=
    build A B D hpos κ hLocal S₀ xs
  refine ⟨T.Vertex, inferInstance, T.system, T.uTransversal, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hCanon χ
  let Liftable (α : RelStructure.Embedding A D) : Prop :=
    Nonempty
      (Partite.Closed.Embedding
        (profile A D α) S₀.system)
  let θ : RelStructure.Embedding A D → κ := fun α =>
    if hα : Liftable α then
      χ (RelStructure.ClosedEmbedding.comp
        f.toRelClosed (profileToRelClosed (Classical.choice hα)))
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ
      (α : RelStructure.Embedding A D)
      (e : Partite.Closed.Embedding (profile A D α) S₀.system) :
      θ α =
        χ (RelStructure.ClosedEmbedding.comp
          f.toRelClosed (profileToRelClosed e)) := by
    have hLift : Liftable α := ⟨e⟩
    simp only [θ, dif_pos hLift]
    have hmem : α ∈ xs := by
      simp [xs]
    exact hf α hmem (Classical.choice hLift) e
  obtain ⟨β, hβ⟩ := hRamsey θ
  let j : RelStructure.ClosedEmbedding B S₀.system.toRelStructure :=
    Partite.HalfClosed.Initial.copyEmbedding B D hpos β
  refine ⟨RelStructure.ClosedEmbedding.comp f.toRelClosed j, ?_⟩
  intro e₁ e₂
  let α₁ : RelStructure.Embedding A D :=
    β.comp e₁.toEmbedding
  let α₂ : RelStructure.Embedding A D :=
    β.comp e₂.toEmbedding
  let p₁ :
      Partite.Closed.Embedding (profile A D α₁) S₀.system :=
    initialProfileCopy A B D hpos β e₁
  let p₂ :
      Partite.Closed.Embedding (profile A D α₂) S₀.system :=
    initialProfileCopy A B D hpos β e₂
  have hmono := hβ e₁.toEmbedding e₂.toEmbedding
  rw [hθ α₁ p₁, hθ α₂ p₂] at hmono
  have hp₁ :
      profileToRelClosed p₁ =
        RelStructure.ClosedEmbedding.comp j e₁ := by
    apply RelStructure.ClosedEmbedding.ext
    intro a
    rfl
  have hp₂ :
      profileToRelClosed p₂ =
        RelStructure.ClosedEmbedding.comp j e₂ := by
    apply RelStructure.ClosedEmbedding.ext
    intro a
    rfl
  rw [hp₁, hp₂] at hmono
  exact hmono

end StructuralRamsey.Partite.Recursive

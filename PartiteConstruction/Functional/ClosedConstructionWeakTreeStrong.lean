import PartiteConstruction.Functional.ClosedPictureWeakTreeStrongStep
import PartiteConstruction.Functional.ClosedConstruction
import PartiteConstruction.Iterated.Initial

/-! # Actual U-closed functional induced construction with iterable weak bound

Every genuine U-closed Picture step preserves the strong relational
LocallyTreeLike invariant on arbitrary weak function-graph substructures.
We carry it through the same finite Hales--Jewett Picture sequence and
closed-copy Ramsey extraction as the full functional Ramsey theorem.

The invariant retains ambient A-copy control, allowing successive complete
induced passes to raise the bounded test size one vertex at a time.
No claim about fibre-surjective tree-completion maps is made.
-/

namespace StructuralRamsey.Partite.Closed.Construction

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}

/-- Run all closed Picture steps with the full controlled weak-tree bound. -/
theorem build_withStrongTree
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (S : Stage B D)
    [Finite U]
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) [Fintype κ]
    {VB : Type v} [Finite VB]
    (Base : RelStructure L.graph VB)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A Base D (n - 1))
    (hS : RelStructure.LocallyTreeLike A Base
      S.system.toRelStructure n) :
    ∃ T : Stage B D,
      CanonicalOn A B D S.system T.system xs κ ∧
      RelStructure.LocallyTreeLike A Base T.system.toRelStructure n := by
  induction xs with
  | nil =>
      refine ⟨S, ?_, hS⟩
      intro χ
      refine ⟨Partite.Closed.Embedding.id S.system, ?_⟩
      intro α h
      exact (List.not_mem_nil h).elim
  | cons α xs ih =>
      obtain ⟨T, hT, hTreeT⟩ := ih
      obtain ⟨Y, hY, C, hPartite, hU, hPicture, hStrongC⟩ :=
        Partite.Closed.Picture.pictureLemma_withStrongTree
          (A := A) (D := D) (B := T.system) (α := α.1)
          Base hA eAB n hn hD hTreeT
          T.isPartite T.uTransversal κ
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hPartite
        uTransversal := hU
      }
      refine ⟨R, ?_, hStrongC⟩
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

/-- Extract the full closed functional Ramsey arrow together with the strong
weak graph-tree invariant of the same chosen U-closed construction. -/
theorem inducedConstruction_withStrongTree
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.ClosedArrow A B D κ)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1)) :
    letI : Nonempty (RelStructure.ClosedEmbedding B D) :=
      nonempty_embedding_of_arrow A B D κ hRamsey
    let S₀ := initialStage B D hpos
    ∃ T : Stage B D,
      RelStructure.ClosedArrow A B T.system.toRelStructure κ ∧
      RelStructure.LocallyTreeLike A B T.system.toRelStructure n := by
  classical
  letI : Nonempty (RelStructure.ClosedEmbedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D hpos
  let xs := allRelevant A B D
  have hInitial :
      RelStructure.LocallyTreeLike A B
        S₀.system.toRelStructure n := by
    exact Partite.Iterated.initial_locallyTreeLike
      A B
      (fun β : RelStructure.ClosedEmbedding B D =>
        β.toEmbedding.toFunctionEmbedding)
      hA.irreducible n
  obtain ⟨T, hCanon, hStrong⟩ :=
    build_withStrongTree A B D S₀ xs κ B hA eAB n hn hD hInitial
  refine ⟨T, ?_, hStrong⟩
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
  let j : RelStructure.ClosedEmbedding B S₀.system.toRelStructure := by
    change RelStructure.ClosedEmbedding B
      (Partite.Closed.Initial.picture B D).toRelStructure
    exact Partite.Closed.Initial.copyEmbedding B D hpos β
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

import PartiteConstruction.Iterated.AttachmentTrace

/-! # Uniform local-tree bound for one support group

The final completion can attach many copies of the base over roots having the
same image support inside the base.  The number of such copies may depend on
the Ramsey witness, so it cannot appear in the local-tree budget.

This file combines labelled-trace selection with the geometric selected-index
witness.  The resulting bound depends only on the requested test size and the
cardinalities of the control and base structures, not on the number of
attached copies.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W I : Type v}
variable {Control : RelStructure L UA}
variable {Base : RelStructure L VB}
variable {Core : RelStructure L W}
variable {S : Set VB}
variable {f : I → Embedding (Base.induce S) Core}

/-- Budget sufficient for one arbitrary finite family of attachments sharing
one support in the base.  The function-space term is exactly
`(n+1)^|Control|`, but retaining it as a finite-cardinal expression avoids
unnecessary arithmetic normalization in downstream proofs. -/
def fixedSupportBudget
    (UA VB : Type v) [Fintype UA] [Fintype VB] (n : ℕ) : ℕ :=
  n + Fintype.card VB * (n + Fintype.card (UA → Option (Fin n)))

/-- An option-valued embedding induced by an embedding of the underlying
types. -/
def optionEmbedding {X Y : Type v} (e : X ↪ Y) : Option X ↪ Option Y where
  toFun
    | none => none
    | some x => some (e x)
  inj' := by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => simp at h
    | some a =>
        cases b with
        | none => simp at h
        | some b =>
            simp only [Option.some.injEq] at h
            exact congrArg some (e.injective h)

/-- Pointwise lifting of an embedding to a function space. -/
def piEmbedding {A X Y : Type v} (e : X ↪ Y) : (A → X) ↪ (A → Y) where
  toFun g := fun a => e (g a)
  inj' := by
    intro g h heq
    funext a
    apply e.injective
    exact congrFun heq a

/-- A simultaneous attachment over one irreducible support preserves local
tree-likeness with a uniform budget independent of the number of copies. -/
theorem attachment_locallyTreeLike_fixedSupport
    [Fintype UA] [Fintype VB] [Finite W] [Fintype I]
    (hControl : Control.Irreducible)
    (hRoot : (Base.induce S).Irreducible)
    (n : ℕ)
    (hCore :
      LocallyTreeLike Control Base Core (fixedSupportBudget UA VB n)) :
    LocallyTreeLike Control Base (Attachment.attach Base S Core f) n := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype ↥S := Fintype.ofFinite ↥S
  intro Test hTest

  obtain ⟨J, hActive, hTrace, hJcard⟩ :=
    exists_selected_indices
      (Control := Control) (Base := Base) (Core := Core) (S := S) (f := f)
      Test

  let corePart : Finset W :=
    Finset.univ.filter (fun w =>
      (Sum.inl w : Attachment.Vertex S (W := W) (I := I)) ∈ Test)
  let rootPairs : Finset (I × ↥S) :=
    J.product (Finset.univ : Finset ↥S)
  let rootPart : Finset W :=
    rootPairs.image (fun p => f p.1 p.2)
  let R : Finset W := corePart ∪ rootPart

  have hCoreTest :
      ∀ w : W,
        (Sum.inl w : Attachment.Vertex S (W := W) (I := I)) ∈ Test →
          w ∈ R := by
    intro w hw
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩

  have hRoots :
      ∀ j : I, j ∈ J → ∀ x : ↥S, f j x ∈ R := by
    intro j hj x
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(j, x), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hj, Finset.mem_univ x⟩

  have hCoreCard : corePart.card ≤ Test.card := by
    let e :
        ↥(↑corePart : Set W) ↪
          ↥(↑Test :
            Set (Attachment.Vertex S (W := W) (I := I))) := {
      toFun := fun w =>
        ⟨Sum.inl w.1, (Finset.mem_filter.mp w.2).2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        have h := congrArg Subtype.val hxy
        exact Sum.inl.inj h
    }
    simpa using Fintype.card_le_of_embedding e

  have hRootPartCard :
      rootPart.card ≤ J.card * Fintype.card ↥S := by
    calc
      rootPart.card ≤ rootPairs.card := by
        exact Finset.card_image_le
      _ = J.card * Fintype.card ↥S := by
        simp [rootPairs]

  have hSupportCard :
      Fintype.card ↥S ≤ Fintype.card VB := by
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

  let TestType :=
    ↥(↑Test :
      Set (Attachment.Vertex S (W := W) (I := I)))
  have hTestTypeCard : Fintype.card TestType ≤ Fintype.card (Fin n) := by
    simpa [TestType] using hTest
  let eTest : TestType ↪ Fin n :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hTestTypeCard)
  let eTrace :
      (UA → Option TestType) ↪ (UA → Option (Fin n)) :=
    piEmbedding (optionEmbedding eTest)
  have hTraceCard :
      Fintype.card (UA → Option TestType) ≤
        Fintype.card (UA → Option (Fin n)) := by
    exact Fintype.card_le_of_embedding eTrace

  have hJuniform :
      J.card ≤ n + Fintype.card (UA → Option (Fin n)) := by
    calc
      J.card ≤ Test.card + Fintype.card (UA → Option TestType) := by
        simpa [TestType, Nat.card_eq_fintype_card] using hJcard
      _ ≤ n + Fintype.card (UA → Option (Fin n)) :=
        Nat.add_le_add hTest hTraceCard

  have hRootsUniform :
      rootPart.card ≤
        Fintype.card VB *
          (n + Fintype.card (UA → Option (Fin n))) := by
    calc
      rootPart.card ≤ J.card * Fintype.card ↥S := hRootPartCard
      _ ≤
          (n + Fintype.card (UA → Option (Fin n))) *
            Fintype.card VB :=
        Nat.mul_le_mul hJuniform hSupportCard
      _ =
          Fintype.card VB *
            (n + Fintype.card (UA → Option (Fin n))) := by
        rw [Nat.mul_comm]

  have hRcard : R.card ≤ fixedSupportBudget UA VB n := by
    calc
      R.card ≤ corePart.card + rootPart.card :=
        Finset.card_union_le corePart rootPart
      _ ≤ Test.card +
          Fintype.card VB *
            (n + Fintype.card (UA → Option (Fin n))) :=
        Nat.add_le_add hCoreCard hRootsUniform
      _ ≤ n +
          Fintype.card VB *
            (n + Fintype.card (UA → Option (Fin n))) :=
        Nat.add_le_add_right hTest _
      _ = fixedSupportBudget UA VB n := rfl

  exact attachmentWitness_of_selected
    (Control := Control) (Base := Base) (Core := Core) (S := S) (f := f)
    hControl hRoot (fixedSupportBudget UA VB n) hCore
    Test J R hRcard hCoreTest hRoots hActive hTrace

end StructuralRamsey.RelStructure.LocallyTreeLike

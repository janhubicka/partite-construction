import PartiteConstruction.Partite.InducedAttachment
import PartiteConstruction.Partite.InducedInitial

/-! # Irreducible-image invariant for the induced construction

Only embeddings of `A` into the base `D` that occur inside a copy of `B`
need to be processed. This is exactly what guarantees that irreducibles inside
the coordinatewise core still project into a copy of `B`.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v w z t
variable {L : RelLanguage.{u}}
variable {U : Type v} {V : Type w} {P : Type z} {X : Type t}
variable (A : RelStructure L U) (B₀ : RelStructure L V) (D₀ : RelStructure L P)

/-- An embedding of `A` into `D` is relevant when it factors through a copy
of `B` in `D`. This is equivalent to the image-containment formulation in
the survey, but carries the factorization needed by the Ramsey extraction. -/
def Relevant (α : RelStructure.Embedding A D₀) : Prop :=
  ∃ (β : RelStructure.Embedding B₀ D₀) (e : RelStructure.Embedding A B₀),
    α = β.comp e

abbrev RelevantEmbedding :=
  {α : RelStructure.Embedding A D₀ // Relevant A B₀ D₀ α}

instance [Finite U] [Finite V] [Finite P] :
    Finite (RelevantEmbedding A B₀ D₀) := by
  infer_instance

namespace System

/-- If all partition labels lie in one fixed copy of `B₀` in `D₀`, then
the irreducible-image invariant is automatic. -/
theorem covers_of_parts_in_copy
    (C : System L P X) (β : RelStructure.Embedding B₀ D₀)
    (hpart : ∀ x : X, ∃ b : V, C.part x = β b) :
    C.CoversIrreduciblesBy B₀ D₀ := by
  intro T _
  exact ⟨β, fun z => hpart z.1⟩

end System

namespace Attachment

variable {Y : Type*} {I : Type*}
variable (C : System L P X) (S : Set X) (E : System L P Y)
variable (f : I → Partite.Embedding (C.induce S) E)

/-- The irreducible-image invariant is preserved by the same free attachment
used in the Picture Lemma. -/
theorem attach_covers
    (hC : C.CoversIrreduciblesBy B₀ D₀)
    (hE : E.CoversIrreduciblesBy B₀ D₀) :
    (Partite.Attachment.attach C S E f).CoversIrreduciblesBy B₀ D₀ := by
  classical
  intro T hT
  have hsplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding) T hT
  rcases hsplit with hcore | ⟨i, hcopy⟩
  · let pre : T → Y := fun s => Classical.choose (hcore s)
    have hpre (s : T) : s.1 = Sum.inl (pre s) :=
      Classical.choose_spec (hcore s)
    let Rng : Set Y := Set.range pre
    have hRng : (E.toRelStructure.induce Rng).Irreducible := by
      intro a b hab
      rcases a.property with ⟨sa, hsa⟩
      rcases b.property with ⟨sb, hsb⟩
      have hsab : sa ≠ sb := by
        intro hs
        apply hab
        apply Subtype.ext
        rw [← hsa, ← hsb, hs]
      obtain ⟨R, z, k, l, hz, hzk, hzl⟩ := hT hsab
      change (Partite.Attachment.attach C S E f).rel R (Subtype.val ∘ z) at hz
      let y : Fin (L.arity R) → Y := fun q => pre (z q)
      have heq : Subtype.val ∘ z = Sum.inl ∘ y := by
        funext q
        exact hpre (z q)
      have hErel : E.rel R y := by
        rw [heq] at hz
        exact (RelStructure.Attachment.core_rel_iff
          (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
          (f := fun j => (f j).toEmbedding) R y).mp hz
      let yR : Fin (L.arity R) → Rng :=
        fun q => ⟨y q, ⟨z q, rfl⟩⟩
      refine ⟨R, yR, k, l, ?_, ?_, ?_⟩
      · exact hErel
      · apply Subtype.ext
        change pre (z k) = a.1
        rw [hzk]
        exact hsa
      · apply Subtype.ext
        change pre (z l) = b.1
        rw [hzl]
        exact hsb
    obtain ⟨β, hβ⟩ := hE Rng hRng
    refine ⟨β, ?_⟩
    intro z
    obtain ⟨b, hb⟩ := hβ ⟨pre z, ⟨z, rfl⟩⟩
    refine ⟨b, ?_⟩
    have hz := hpre z
    change Partite.Attachment.part C S E (z.1) = β b
    calc
      Partite.Attachment.part C S E z.1 =
          Partite.Attachment.part C S E (Sum.inl (pre z)) :=
        congrArg (Partite.Attachment.part C S E) hz
      _ = E.part (pre z) := rfl
      _ = β b := hb
  · let pre : T → X := fun s => Classical.choose (hcopy s)
    have hpre (s : T) : s.1 =
        RelStructure.Attachment.copyMap C.toRelStructure S E.toRelStructure
          (fun j => (f j).toEmbedding) i (pre s) :=
      Classical.choose_spec (hcopy s)
    let Rng : Set X := Set.range pre
    have hRng : (C.toRelStructure.induce Rng).Irreducible := by
      intro a b hab
      rcases a.property with ⟨sa, hsa⟩
      rcases b.property with ⟨sb, hsb⟩
      have hsab : sa ≠ sb := by
        intro hs
        apply hab
        apply Subtype.ext
        rw [← hsa, ← hsb, hs]
      obtain ⟨R, z, k, l, hz, hzk, hzl⟩ := hT hsab
      change (Partite.Attachment.attach C S E f).rel R (Subtype.val ∘ z) at hz
      let y : Fin (L.arity R) → X := fun q => pre (z q)
      have heq :
          Subtype.val ∘ z =
            RelStructure.Attachment.copyMap C.toRelStructure S E.toRelStructure
              (fun j => (f j).toEmbedding) i ∘ y := by
        funext q
        exact hpre (z q)
      have hCrel : C.rel R y := by
        rw [heq] at hz
        exact (RelStructure.Attachment.copy_rel_iff
          (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
          (f := fun j => (f j).toEmbedding) i R y).mp hz
      let yR : Fin (L.arity R) → Rng :=
        fun q => ⟨y q, ⟨z q, rfl⟩⟩
      refine ⟨R, yR, k, l, ?_, ?_, ?_⟩
      · exact hCrel
      · apply Subtype.ext
        change pre (z k) = a.1
        rw [hzk]
        exact hsa
      · apply Subtype.ext
        change pre (z l) = b.1
        rw [hzl]
        exact hsb
    obtain ⟨β, hβ⟩ := hC Rng hRng
    refine ⟨β, ?_⟩
    intro z
    obtain ⟨b, hb⟩ := hβ ⟨pre z, ⟨z, rfl⟩⟩
    refine ⟨b, ?_⟩
    have hz := hpre z
    change Partite.Attachment.part C S E z.1 = β b
    calc
      Partite.Attachment.part C S E z.1 =
          Partite.Attachment.part C S E
            (RelStructure.Attachment.copyMap C.toRelStructure S E.toRelStructure
              (fun j => (f j).toEmbedding) i (pre z)) :=
        congrArg (Partite.Attachment.part C S E) hz
      _ = C.part (pre z) :=
        Partite.Attachment.part_copyMap C S E f i (pre z)
      _ = β b := hb

end Attachment

/-- Relabelling any system over `A` along a relevant embedding puts every
part of the core inside the witnessing copy of `B₀` in `D₀`. -/
theorem relabel_covers_of_relevant
    {Y : Type*} (E : System L U Y)
    (α : RelevantEmbedding A B₀ D₀) :
    (E.relabel α.1.toFunctionEmbedding).CoversIrreduciblesBy B₀ D₀ := by
  rcases α.2 with ⟨β, e, hfac⟩
  apply System.covers_of_parts_in_copy B₀ D₀ _ β
  intro y
  refine ⟨e (E.part y), ?_⟩
  change α.1 (E.part y) = β (e (E.part y))
  rw [hfac]
  rfl

end StructuralRamsey.Partite.Induced

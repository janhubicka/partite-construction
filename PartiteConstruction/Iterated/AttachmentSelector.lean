import PartiteConstruction.Iterated.TraceSelector
import PartiteConstruction.Relational.Attachment

/-! # Selecting attachment indices from a finite test

For one fixed-support multi-copy attachment, select a bounded family of copy
indices sufficient for a tested finite set:

* all indices that contribute an outside tested vertex;
* one representative index for every labelled trace of an ambient
  `Control`-copy contained in an attached copy.

The trace remembers, for each labelled control vertex, its actual tested
vertex when present.  Equality of traces therefore gives exactly the
replacement condition used by `attachmentWitness_of_selected`.
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

/-- An ambient control-copy lies in one of the attached copies. -/
def LiesInAttachedCopy
    (α : Embedding Control (Attachment.attach Base S Core f)) : Prop :=
  ∃ i : I, ∀ a : UA, ∃ b : VB,
    α a = Attachment.copyMap Base S Core f i b

/-- Select boundedly many attached copies that cover active outside vertices
and all realized labelled control traces. -/
theorem selectAttachmentIndices
    [Finite UA] [Finite VB] [Finite W] [Fintype I]
    (Test : Finset (Attachment.Vertex S (W := W) (I := I))) :
    ∃ J : Finset I,
      J.card ≤ Test.card + (Test.card + 1) ^ Nat.card UA ∧
      (∀ i : I, ∀ x : {x : VB // x ∉ S},
        (Sum.inr (i, x) : Attachment.Vertex S (W := W) (I := I)) ∈ Test →
          i ∈ J) ∧
      ∀ α : Embedding Control (Attachment.attach Base S Core f),
        LiesInAttachedCopy (Base := Base) (S := S) (Core := Core) (f := f) α →
        ∃ j : I, j ∈ J ∧
          ∃ β : Embedding Control Base,
            ∀ a : UA, α a ∈ Test →
              α a = Attachment.copyMap Base S Core f j (β a) := by
  classical
  letI : Fintype UA := Fintype.ofFinite UA
  let TestV := ↥(↑Test :
    Set (Attachment.Vertex S (W := W) (I := I)))
  let X :=
    {α : Embedding Control (Attachment.attach Base S Core f) //
      LiesInAttachedCopy (Base := Base) (S := S)
        (Core := Core) (f := f) α}
  letI : Fintype TestV := Fintype.ofFinite TestV
  letI : Fintype X := Fintype.ofFinite X

  let idx : X → I := fun x => Classical.choose x.2
  have hidx (x : X) :
      ∀ a : UA, ∃ b : VB,
        x.1 a = Attachment.copyMap Base S Core f (idx x) b :=
    Classical.choose_spec x.2

  let trace : X → UA → Option TestV := fun x a =>
    if h : x.1 a ∈ Test then some ⟨x.1 a, h⟩ else none

  let active : Finset I :=
    Finset.univ.filter (fun i =>
      ∃ x : {x : VB // x ∉ S},
        (Sum.inr (i, x) :
          Attachment.Vertex S (W := W) (I := I)) ∈ Test)

  have hactiveCard : active.card ≤ Test.card := by
    let Active := {i : I // i ∈ active}
    let outWitness (i : Active) :
        {x : VB // x ∉ S} :=
      Classical.choose (by
        have hi := i.2
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi)
    have houtWitness (i : Active) :
        (Sum.inr (i.1, outWitness i) :
          Attachment.Vertex S (W := W) (I := I)) ∈ Test :=
      Classical.choose_spec (by
        have hi := i.2
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi)
    let out : Active → TestV := fun i =>
      ⟨Sum.inr (i.1, outWitness i), houtWitness i⟩
    have houtInj : Function.Injective out := by
      intro i j hij
      apply Subtype.ext
      have hv := congrArg Subtype.val hij
      have hp := Sum.inr.inj hv
      exact congrArg Prod.fst hp
    have hcard : Fintype.card Active ≤ Fintype.card TestV :=
      Fintype.card_le_of_injective out houtInj
    simpa [Active, TestV] using hcard

  obtain ⟨J, hactiveSub, hJcard, hrep⟩ :=
    StructuralRamsey.FiniteTrace.selectIndices_cardBound
      idx trace active Test.card hactiveCard (by
        simp [TestV])

  refine ⟨J, ?_, ?_, ?_⟩
  · simpa [Nat.card_eq_fintype_card] using hJcard
  · intro i x hx
    apply hactiveSub
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx⟩
  · intro α hα
    let x : X := ⟨α, hα⟩
    obtain ⟨y, hyJ, htrace⟩ := hrep x
    let j : I := idx y
    have hyrange :
        ∀ a : UA, ∃ b : VB,
          y.1 a = Attachment.copyEmbedding Base S Core f j b := by
      intro a
      obtain ⟨b, hb⟩ := hidx y a
      exact ⟨b, hb⟩
    let β : Embedding Control Base :=
      y.1.factorThroughRange
        (Attachment.copyEmbedding Base S Core f j) hyrange
    refine ⟨j, hyJ, β, ?_⟩
    intro a ha
    have ht := congrFun htrace a
    have hxy : x.1 a = y.1 a := by
      by_cases hy : y.1 a ∈ Test
      · have ht' := ht
        simp only [trace, dif_pos ha, dif_pos hy] at ht'
        have hs := Option.some.inj ht'.symm
        exact congrArg Subtype.val hs
      · have ht' := ht
        simp only [trace, dif_pos ha, dif_neg hy] at ht'
        contradiction
    have hycopy :
        y.1 a = Attachment.copyMap Base S Core f j (β a) := by
      change y.1 a =
        Attachment.copyEmbedding Base S Core f j (β a)
      exact Classical.choose_spec (hyrange a)
    exact hxy.trans hycopy

end StructuralRamsey.RelStructure.LocallyTreeLike

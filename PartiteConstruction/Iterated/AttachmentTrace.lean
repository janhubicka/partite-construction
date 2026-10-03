import PartiteConstruction.Iterated.UniformAttachment

/-! # Trace representatives for a fixed-support attachment

For a finite tested set, an ambient copy of the control structure is relevant
only through the labelled trace of its vertices on that tested set.  There are
at most `(|Test|+1)^|Control|` such traces.

For the simultaneous attachment of copies of `Base` along a fixed support,
we select
* every index contributing an outside tested vertex, and
* one attachment index representing every realized labelled control trace.

The geometric theorem in `UniformAttachment` can then be applied using only
the roots of these selected indices.
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

/-- Labelled intersection trace of an embedding on a finite tested set. -/
noncomputable def testTrace
    (Test : Finset (Attachment.Vertex S (W := W) (I := I)))
    (α : Embedding Control (Attachment.attach Base S Core f)) :
    UA → Option ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))) := by
  classical
  exact fun a =>
    if ha : α a ∈ Test then some ⟨α a, ha⟩ else none

/-- Equal traces agree on every tested labelled control vertex. -/
theorem eq_of_testTrace_eq
    (Test : Finset (Attachment.Vertex S (W := W) (I := I)))
    {α β : Embedding Control (Attachment.attach Base S Core f)}
    (h : testTrace Test α = testTrace Test β)
    (a : UA) (ha : α a ∈ Test) :
    β a ∈ Test ∧ α a = β a := by
  classical
  have hfun := congrFun h a
  change
    (if hα : α a ∈ Test then
      some (⟨α a, hα⟩ :
        ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))))
     else none) =
    (if hβ : β a ∈ Test then
      some (⟨β a, hβ⟩ :
        ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))))
     else none) at hfun
  by_cases hb : β a ∈ Test
  · rw [dif_pos ha, dif_pos hb] at hfun
    have hsub : (⟨α a, ha⟩ :
        ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I)))) =
      ⟨β a, hb⟩ := Option.some.inj hfun
    exact ⟨hb, congrArg Subtype.val hsub⟩
  · rw [dif_pos ha, dif_neg hb] at hfun
    cases hfun

/-- There is a uniformly bounded set of attachment indices containing all
active indices and one representative for every labelled control trace
realized inside an attached copy. -/
theorem exists_selected_indices
    [Fintype UA] [Finite VB] [Finite W] [Fintype I]
    (Test : Finset (Attachment.Vertex S (W := W) (I := I))) :
    ∃ J : Finset I,
      (∀ i : I, ∀ x : {x : VB // x ∉ S},
        (Sum.inr (i, x) : Attachment.Vertex S (W := W) (I := I)) ∈ Test →
          i ∈ J) ∧
      (∀ α : Embedding Control (Attachment.attach Base S Core f),
        (∃ i : I, ∀ a : UA, ∃ b : VB,
          α a = Attachment.copyMap Base S Core f i b) →
        ∃ j : I, j ∈ J ∧
          ∃ β : Embedding Control Base,
            ∀ a : UA, α a ∈ Test →
              α a = Attachment.copyMap Base S Core f j (β a)) ∧
      J.card ≤ Test.card +
        Fintype.card
          (UA → Option ↥(↑Test :
            Set (Attachment.Vertex S (W := W) (I := I)))) := by
  classical
  let Whole := Attachment.attach Base S Core f
  let active : Finset I :=
    Finset.univ.filter (fun i =>
      ∃ x : {x : VB // x ∉ S},
        (Sum.inr (i, x) : Attachment.Vertex S (W := W) (I := I)) ∈ Test)
  let CopyAmbient :=
    {α : Embedding Control Whole //
      ∃ i : I, ∀ a : UA, ∃ b : VB,
        α a = Attachment.copyMap Base S Core f i b}
  letI : Fintype CopyAmbient := Fintype.ofFinite CopyAmbient
  let Trace :=
    UA → Option ↥(↑Test :
      Set (Attachment.Vertex S (W := W) (I := I)))
  letI : Fintype Trace := Fintype.ofFinite Trace
  let traces : Finset Trace :=
    Finset.univ.image (fun α : CopyAmbient => testTrace Test α.1)

  let repAmbient (τ : ↥(↑traces : Set Trace)) : CopyAmbient :=
    Classical.choose (by
      rcases Finset.mem_image.mp τ.2 with ⟨α, _, hα⟩
      exact ⟨α, hα⟩)
  have hrepAmbient (τ : ↥(↑traces : Set Trace)) :
      testTrace Test (repAmbient τ).1 = τ.1 :=
    Classical.choose_spec (by
      rcases Finset.mem_image.mp τ.2 with ⟨α, _, hα⟩
      exact ⟨α, hα⟩)

  let repIndex (τ : ↥(↑traces : Set Trace)) : I :=
    Classical.choose (repAmbient τ).2
  have hrepIndex (τ : ↥(↑traces : Set Trace)) :
      ∀ a : UA, ∃ b : VB,
        (repAmbient τ).1 a =
          Attachment.copyMap Base S Core f (repIndex τ) b :=
    Classical.choose_spec (repAmbient τ).2

  let reps : Finset I :=
    Finset.univ.image repIndex
  let J : Finset I := active ∪ reps
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i x hx
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨x, hx⟩⟩
  · intro α hαcopy
    let αc : CopyAmbient := ⟨α, hαcopy⟩
    let τ : Trace := testTrace Test α
    have hτ : τ ∈ traces := by
      apply Finset.mem_image.mpr
      exact ⟨αc, Finset.mem_univ _, rfl⟩
    let τs : ↥(↑traces : Set Trace) := ⟨τ, hτ⟩
    let j : I := repIndex τs
    have hjrep : j ∈ reps := by
      apply Finset.mem_image.mpr
      exact ⟨τs, Finset.mem_univ _, rfl⟩
    have hj : j ∈ J := Finset.mem_union_right _ hjrep
    have hrange : ∀ a : UA, ∃ b : VB,
        (repAmbient τs).1 a =
          Attachment.copyEmbedding Base S Core f j b := by
      intro a
      exact hrepIndex τs a
    let β : Embedding Control Base :=
      (repAmbient τs).1.factorThroughRange
        (Attachment.copyEmbedding Base S Core f j) hrange
    refine ⟨j, hj, β, ?_⟩
    intro a ha
    have htraceEq :
        testTrace Test α = testTrace Test (repAmbient τs).1 := by
      change τ = testTrace Test (repAmbient τs).1
      exact (hrepAmbient τs).symm
    obtain ⟨hmemRep, heq⟩ :=
      eq_of_testTrace_eq Test htraceEq a ha
    have hβspec :
        (repAmbient τs).1 a =
          Attachment.copyEmbedding Base S Core f j (β a) := by
      change (repAmbient τs).1 a =
        Attachment.copyEmbedding Base S Core f j
          (Classical.choose (hrange a))
      exact Classical.choose_spec (hrange a)
    exact heq.trans hβspec
  · have hactiveCard : active.card ≤ Test.card := by
      let pick :
          ↥(↑active : Set I) →
            ↥(↑Test :
              Set (Attachment.Vertex S (W := W) (I := I))) :=
        fun i =>
          let x := Classical.choose (Finset.mem_filter.mp i.2).2
          ⟨Sum.inr (i.1, x),
            Classical.choose_spec (Finset.mem_filter.mp i.2).2⟩
      have hpick : Function.Injective pick := by
        intro i j hij
        apply Subtype.ext
        have hval := congrArg Subtype.val hij
        change
          (Sum.inr
            (i.1, Classical.choose (Finset.mem_filter.mp i.2).2) :
              Attachment.Vertex S (W := W) (I := I)) =
          Sum.inr
            (j.1, Classical.choose (Finset.mem_filter.mp j.2).2) at hval
        exact congrArg Prod.fst (Sum.inr.inj hval)
      have hcard := Fintype.card_le_of_injective pick hpick
      simpa using hcard
    have hrepsCard : reps.card ≤ traces.card := by
      calc
        reps.card ≤ Fintype.card ↥(↑traces : Set Trace) := by
          simpa [reps] using
            (Finset.card_image_le :
              (Finset.univ.image repIndex).card ≤
                (Finset.univ : Finset ↥(↑traces : Set Trace)).card)
        _ = traces.card := by simp
    have htracesCard : traces.card ≤ Fintype.card Trace := by
      simpa using (Finset.card_le_card (Finset.subset_univ traces))
    calc
      J.card ≤ active.card + reps.card := Finset.card_union_le active reps
      _ ≤ Test.card + Fintype.card Trace :=
        Nat.add_le_add hactiveCard (hrepsCard.trans htracesCard)

end StructuralRamsey.RelStructure.LocallyTreeLike

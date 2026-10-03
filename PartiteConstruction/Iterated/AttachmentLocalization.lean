import PartiteConstruction.Iterated.UniformAttachment
import PartiteConstruction.Iterated.FinalCompletion

/-! # Localization through a simultaneous fixed-support attachment

The final completion invariant says every irreducible in the current
extension lies either in the embedded original core or in a copy of Base.
This remains true when arbitrarily many Base-copies are attached
simultaneously over one support.
-/
namespace StructuralRamsey.RelStructure.FinalCompletion

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {O VB W I : Type v}
variable {Orig : RelStructure L O}
variable {Base : RelStructure L VB}
variable {Current : RelStructure L W}
variable {S : Set VB}
variable {f : I → Embedding (Base.induce S) Current}

/-- Core-or-base localization is preserved by a simultaneous attachment. -/
theorem coreOrBase_attachment
    {j : Embedding Orig Current}
    (h : CoreOrBase (Orig := Orig) (Base := Base) j) :
    CoreOrBase (Orig := Orig) (Base := Base)
      ((Attachment.coreEmbedding Base S Current f).comp j) := by
  classical
  let Whole := Attachment.attach Base S Current f
  intro T hT
  let inc : Embedding (Whole.induce T) Whole :=
    inclusion Whole T
  rcases Attachment.irreducible_core_or_copy
      (B := Base) (S := S) (D := Current) (f := f) T hT with
    hcore | ⟨i, hcopy⟩
  · have hrange :
        ∀ z : T, ∃ w : W,
          inc z = Attachment.coreEmbedding Base S Current f w := by
      intro z
      obtain ⟨w, hw⟩ := hcore z
      exact ⟨w, hw⟩
    let eCurrent : Embedding (Whole.induce T) Current :=
      inc.factorThroughRange
        (Attachment.coreEmbedding Base S Current f) hrange
    let Rng : Set W := Set.range eCurrent
    have hRng : (Current.induce Rng).Irreducible :=
      hT.range_embedding eCurrent
    rcases h Rng hRng with hOrig | ⟨β, hβ⟩
    · left
      intro z
      let q : Rng := ⟨eCurrent z, ⟨z, rfl⟩⟩
      obtain ⟨o, ho⟩ := hOrig q
      refine ⟨o, ?_⟩
      have hz := Classical.choose_spec (hrange z)
      change
        z.1 = Attachment.coreEmbedding Base S Current f (j o)
      calc
        z.1 = inc z := rfl
        _ = Attachment.coreEmbedding Base S Current f (eCurrent z) := hz
        _ = Attachment.coreEmbedding Base S Current f (j o) :=
          congrArg (Attachment.coreEmbedding Base S Current f) ho
    · right
      refine
        ⟨(Attachment.coreEmbedding Base S Current f).comp β, ?_⟩
      intro z
      let q : Rng := ⟨eCurrent z, ⟨z, rfl⟩⟩
      obtain ⟨b, hb⟩ := hβ q
      refine ⟨b, ?_⟩
      have hz := Classical.choose_spec (hrange z)
      change
        z.1 =
          Attachment.coreEmbedding Base S Current f (β b)
      calc
        z.1 = inc z := rfl
        _ = Attachment.coreEmbedding Base S Current f (eCurrent z) := hz
        _ = Attachment.coreEmbedding Base S Current f (β b) :=
          congrArg (Attachment.coreEmbedding Base S Current f) hb
  · right
    refine ⟨Attachment.copyEmbedding Base S Current f i, ?_⟩
    intro z
    obtain ⟨b, hb⟩ := hcopy z
    exact ⟨b, hb⟩

end StructuralRamsey.RelStructure.FinalCompletion

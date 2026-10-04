import PartiteConstruction.Structure.RootedOrder
import PartiteConstruction.Structure.RootedCanonical
import PartiteConstruction.Structure.RootedClass
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions

set_option autoImplicit false

/-! # Ramsey transfer through the canonical fixed-root reduction

This removes the positive-function-arity hypothesis from the functional EHN
theorem by applying the checked positive-arity theorem to the moving language
over the canonical finite root.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R U V : Type v}

/-- Reattaching the root commutes with composition with a root-compatible
ordered embedding. -/
theorem liftOrderedEmbedding_comp
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    [Fintype R] [LinearOrder R]
    [Fintype U] [LinearOrder U] [Fintype V] [LinearOrder V]
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (hρA : StrictMono ρA) (hρB : StrictMono ρB)
    {W : Type v} {C : Structure (language L R) W}
    [Fintype W] [LinearOrder W]
    (f : Structure.Embedding (encode ρB).withLinearOrder C.withLinearOrder)
    (e : Structure.Embedding A.withLinearOrder B.withLinearOrder)
    (hroot : ∀ r, e.linearOrderReduct (ρA r) = ρB r) :
    liftOrderedEmbedding ρA hρA
        (f.comp (encodeOrderedEmbedding e hroot)) =
      (liftOrderedEmbedding ρB hρB f).comp e := by
  apply Structure.Embedding.ext
  intro a
  rw [liftOrderedEmbedding_apply, Structure.Embedding.comp_apply,
    liftOrderedEmbedding_apply]
  have hs : split ρB (e a) =
      sumMap (outsideMap e.linearOrderReduct hroot) (split ρA a) := by
    change split ρB (e.linearOrderReduct a) =
      sumMap (outsideMap e.linearOrderReduct hroot) (split ρA a)
    exact split_embedding e.linearOrderReduct hroot a
  rw [hs]
  cases h : split ρA a with
  | inl r =>
      simp [sumMap, Structure.Embedding.comp_apply]
  | inr x =>
      rfl

/-- Functional EHN for arbitrary arities, including constants. -/
theorem Structure.FreeAmalgamationClass.orderedRamsey_allArity
    {K : Structure.StructureClass.{u,v} (L := L)}
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : K A) (hB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : Structure L W),
      K C ∧ Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  by_cases hcopy :
      Nonempty (Structure.Embedding A.withLinearOrder B.withLinearOrder)
  · obtain ⟨e₀⟩ := hcopy
    let Root : Structure L A.nullaryRoot := canonicalRoot A
    let ρA : Structure.Embedding Root A := canonicalRootEmbedding A
    let ρB : Structure.Embedding Root B :=
      e₀.linearOrderReduct.comp ρA
    letI : Fintype A.nullaryRoot := Fintype.ofFinite _
    have hρA : StrictMono ρA := canonicalRootEmbedding_strictMono A
    have hρB : StrictMono ρB := e₀.strictMono.comp hρA
    have hKA : decodedClass Root K (encode ρA) :=
      encode_mem_decodedClass ρA hK hA
    have hKB : decodedClass Root K (encode ρB) :=
      encode_mem_decodedClass ρB hK hB
    obtain ⟨W, hW, oW, C, hC, hRamsey⟩ :=
      (decodedClass_free Root hK).orderedRamsey
        (encode ρA) (encode ρB) hKA hKB
        (language_positive L A.nullaryRoot) κ
    letI : Finite W := hW
    letI : Fintype W := Fintype.ofFinite W
    letI : LinearOrder W := oW
    let o : LinearOrder (Sum A.nullaryRoot W) :=
      reconstructedOrder Root C
    refine ⟨Sum A.nullaryRoot W, inferInstance, o, decode Root C, hC, ?_⟩
    intro χ
    let θ :
        Structure.Embedding (encode ρA).withLinearOrder C.withLinearOrder → κ :=
      fun f => χ (liftOrderedEmbedding ρA hρA f)
    obtain ⟨f, hf⟩ := hRamsey θ
    let f' := liftOrderedEmbedding ρB hρB f
    refine ⟨f', ?_⟩
    intro e₁ e₂
    have hroot₁ : ∀ r,
        e₁.linearOrderReduct (ρA r) = ρB r := by
      intro r
      calc
        e₁.linearOrderReduct (ρA r) =
            e₀.linearOrderReduct (ρA r) := by
          simpa only [ρA] using orderedEmbedding_agrees_on_root e₀ e₁ r
        _ = ρB r := rfl
    have hroot₂ : ∀ r,
        e₂.linearOrderReduct (ρA r) = ρB r := by
      intro r
      calc
        e₂.linearOrderReduct (ρA r) =
            e₀.linearOrderReduct (ρA r) := by
          simpa only [ρA] using orderedEmbedding_agrees_on_root e₀ e₂ r
        _ = ρB r := rfl
    have hm := hf
      (encodeOrderedEmbedding e₁ hroot₁)
      (encodeOrderedEmbedding e₂ hroot₂)
    change
      χ (liftOrderedEmbedding ρA hρA
        (f.comp (encodeOrderedEmbedding e₁ hroot₁))) =
      χ (liftOrderedEmbedding ρA hρA
        (f.comp (encodeOrderedEmbedding e₂ hroot₂))) at hm
    rw [liftOrderedEmbedding_comp hρA hρB f e₁ hroot₁,
      liftOrderedEmbedding_comp hρA hρB f e₂ hroot₂] at hm
    exact hm
  · refine ⟨V, inferInstance, inferInstance, B, hB, ?_⟩
    intro χ
    refine ⟨Structure.Embedding.id B.withLinearOrder, ?_⟩
    intro e₁ e₂
    exact (hcopy ⟨e₁⟩).elim

end StructuralRamsey.Rooted

import PartiteConstruction.Structure.RootedSplit

set_option autoImplicit false

/-! # Correctness of encode/decode on a rooted structure -/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R U : Type v}

@[simp] theorem split_root
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (r : R) :
    split ρ (ρ r) = Sum.inl r := by
  classical
  have h : ρ r ∈ Set.range ρ := ⟨r, rfl⟩
  simp only [split, dif_pos h]
  apply congrArg Sum.inl
  exact ρ.injective (Classical.choose_spec h)

@[simp] theorem split_outside
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (x : Outside ρ) :
    split ρ x.1 = Sum.inr x := by
  classical
  simp [split, x.2]

theorem mem_image_split_inl
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (S : Set U) (r : R) :
    Sum.inl r ∈ Structure.imageSet (split ρ) S ↔ ρ r ∈ S := by
  constructor
  · rintro ⟨a, ha, hsplit⟩
    have hu := congrArg (unsplit ρ) hsplit
    simpa using hu ▸ ha
  · intro hr
    exact ⟨ρ r, hr, split_root ρ r⟩

theorem mem_image_split_inr
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (S : Set U) (x : Outside ρ) :
    Sum.inr x ∈ Structure.imageSet (split ρ) S ↔ x.1 ∈ S := by
  constructor
  · rintro ⟨a, ha, hsplit⟩
    have hu := congrArg (unsplit ρ) hsplit
    simpa using hu ▸ ha
  · intro hx
    exact ⟨x.1, hx, split_outside ρ x⟩

theorem mem_image_embedding_iff
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (S : Set R) (r : R) :
    ρ r ∈ Structure.imageSet ρ S ↔ r ∈ S := by
  constructor
  · rintro ⟨s, hs, hsr⟩
    exact ρ.injective hsr ▸ hs
  · intro hr
    exact ⟨r, hr, rfl⟩

/-- The original rooted structure is fully embedded into decode(encode(A)) by
the canonical carrier split.  Since the split is bijective, this is the
structural isomorphism underlying the elimination of constants. -/
noncomputable def splitEmbedding
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A) :
    Structure.Embedding A (decode Root (encode ρ)) where
  toFun := split ρ
  injective := (splitEquiv ρ).injective
  map_rel_iff := by
    intro S x
    let t := split ρ ∘ x
    by_cases h : (Pattern.ofTuple t).HasMoving
    · have hfill := fill_pad_split ρ x h
      simp only [decode, dif_pos h, encode]
      rw [hfill]
    · have hroot := rootTuple_split ρ x h
      simp only [decode, dif_neg h]
      rw [← ρ.map_rel_iff S (Pattern.rootTuple t h), hroot]
  map_func := by
    intro F x
    let t := split ρ ∘ x
    by_cases h : (Pattern.ofTuple t).HasMoving
    · have hfill := fill_pad_split ρ x h
      ext z
      cases z with
      | inl r =>
          rw [mem_image_split_inl ρ]
          simp only [decode, dif_pos h, encode]
          rw [hfill]
      | inr y =>
          rw [mem_image_split_inr ρ]
          simp only [decode, dif_pos h, encode]
          have hargs :
              (fun i =>
                (Structure.funcTuple (Pattern.pad t h)
                  (Pattern.dummy t h)) i.castSucc) =
                Pattern.pad t h := by
            funext i
            rw [Structure.funcTuple_castSucc]
          rw [hargs, hfill]
    · have hroot := rootTuple_split ρ x h
      ext z
      cases z with
      | inl r =>
          rw [mem_image_split_inl ρ]
          simp only [decode, dif_neg h]
          have hm := ρ.map_func F (Pattern.rootTuple t h)
          rw [hroot] at hm
          rw [← hm, mem_image_embedding_iff ρ]
      | inr y =>
          rw [mem_image_split_inr ρ]
          simp only [decode, dif_neg h]
          constructor
          · intro hy
            have hm := ρ.map_func F (Pattern.rootTuple t h)
            rw [hroot] at hm
            have hy' := hy
            rw [← hm] at hy'
            rcases hy' with ⟨r, hr, hyr⟩
            exact False.elim (y.2 ⟨r, hyr⟩)
          · intro hf
            exact False.elim hf

theorem splitEmbedding_surjective
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A) :
    Function.Surjective (splitEmbedding ρ) :=
  (splitEquiv ρ).surjective

end StructuralRamsey.Rooted

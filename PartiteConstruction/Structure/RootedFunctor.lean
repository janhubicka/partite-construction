import PartiteConstruction.Structure.RootedReduction

set_option autoImplicit false

/-! # Functoriality of the rooted reduction -/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v

variable {L : Language.{u}} {R V W : Type v}

theorem Pattern.not_hasMoving_inl {n : ℕ} (x : Fin n → R) :
    ¬(Pattern.ofTuple (Sum.inl ∘ x : Fin n → Sum R V)).HasMoving := by
  rw [Pattern.ofTuple_hasMoving_iff]
  rintro ⟨i, y, h⟩
  exact Sum.noConfusion h

/-- The fixed root is a full substructure of every decoded structure. -/
noncomputable def rootEmbedding
    (Root : Structure L R) (C : Structure (language L R) V) :
    Structure.Embedding Root (decode Root C) where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel_iff := by
    intro S x
    have hm := Pattern.not_hasMoving_inl (V := V) x
    have hx := Pattern.rootTuple_inl (V := V) x hm
    simp [decode, hm, hx]
  map_func := by
    intro F x
    have hm := Pattern.not_hasMoving_inl (V := V) x
    have hx := Pattern.rootTuple_inl (V := V) x hm
    ext y
    cases y with
    | inl r =>
        simp [Structure.imageSet, decode, hm, hx]
    | inr y =>
        simp [Structure.imageSet, decode, hm, hx]

/-- Decoding sends a full moving embedding to a full embedding fixing the
root pointwise. -/
noncomputable def decodeEmbedding
    (Root : Structure L R)
    {C : Structure (language L R) V}
    {D : Structure (language L R) W}
    (e : Structure.Embedding C D) :
    Structure.Embedding (decode Root C) (decode Root D) where
  toFun := sumMap e
  injective := sumMap_injective e.injective
  map_rel_iff := by
    intro S t
    by_cases h : (Pattern.ofTuple t).HasMoving
    · have h' : (Pattern.ofTuple (sumMap e ∘ t)).HasMoving := by
        exact (Pattern.hasMoving_sumMap e t).2 h
      have hp := Pattern.ofTuple_sumMap e t
      have hpad := Pattern.pad_sumMap e t h h'
      simp only [decode, dif_pos h, dif_pos h']
      rw [hp, hpad]
      exact e.map_rel_iff (.base S (Pattern.ofTuple t)) (Pattern.pad t h)
    · have h' : ¬(Pattern.ofTuple (sumMap e ∘ t)).HasMoving :=
        fun ht => h ((Pattern.hasMoving_sumMap e t).1 ht)
      have hr := Pattern.rootTuple_sumMap e t h h'
      simp only [decode, dif_neg h, dif_neg h']
      rw [hr]
  map_func := by
    intro F t
    by_cases h : (Pattern.ofTuple t).HasMoving
    · have h' : (Pattern.ofTuple (sumMap e ∘ t)).HasMoving :=
        (Pattern.hasMoving_sumMap e t).2 h
      have hp := Pattern.ofTuple_sumMap e t
      have hpad := Pattern.pad_sumMap e t h h'
      have hdummy := Pattern.dummy_sumMap e t h h'
      have hargs :
          Structure.funcTuple (Pattern.pad (sumMap e ∘ t) h')
              (Pattern.dummy (sumMap e ∘ t) h') =
            e ∘ Structure.funcTuple (Pattern.pad t h) (Pattern.dummy t h) := by
        rw [hpad, hdummy]
        exact (Structure.comp_funcTuple e (Pattern.pad t h)
          (Pattern.dummy t h)).symm
      ext y
      cases y with
      | inl r =>
          simp only [Structure.imageSet, decode, dif_pos h, dif_pos h']
          constructor
          · rintro ⟨z, hz, heq⟩
            cases z with
            | inl s =>
                have hs : s = r := by simpa [sumMap] using heq
                subst s
                change
                  D.rel
                    (.output F (Pattern.ofTuple (sumMap e ∘ t)) r)
                    (Pattern.pad (sumMap e ∘ t) h')
                rw [hp, hpad]
                exact
                  (e.map_rel_iff
                    (.output F (Pattern.ofTuple t) r)
                    (Pattern.pad t h)).mpr hz
            | inr z => simp [sumMap] at heq
          · intro hz
            refine ⟨Sum.inl r, ?_, rfl⟩
            change
              C.rel (.output F (Pattern.ofTuple t) r) (Pattern.pad t h)
            have hz' := hz
            change
              D.rel
                (.output F (Pattern.ofTuple (sumMap e ∘ t)) r)
                (Pattern.pad (sumMap e ∘ t) h') at hz'
            rw [hp, hpad] at hz'
            exact
              (e.map_rel_iff
                (.output F (Pattern.ofTuple t) r)
                (Pattern.pad t h)).mp hz'
      | inr y =>
          simp only [Structure.imageSet, decode, dif_pos h, dif_pos h']
          constructor
          · rintro ⟨z, hz, heq⟩
            cases z with
            | inl r => simp [sumMap] at heq
            | inr x =>
                have hxy : e x = y := by simpa [sumMap] using heq
                change
                  y ∈ D.func
                    ⟨F, Pattern.ofTuple (sumMap e ∘ t)⟩
                    (Structure.funcTuple
                      (Pattern.pad (sumMap e ∘ t) h')
                      (Pattern.dummy (sumMap e ∘ t) h'))
                rw [hp, hargs]
                have himg :
                    e x ∈ Structure.imageSet e
                      (C.func ⟨F, Pattern.ofTuple t⟩
                        (Structure.funcTuple (Pattern.pad t h)
                          (Pattern.dummy t h))) :=
                  ⟨x, hz, rfl⟩
                rw [e.map_func ⟨F, Pattern.ofTuple t⟩
                  (Structure.funcTuple (Pattern.pad t h)
                    (Pattern.dummy t h))] at himg
                rwa [hxy] at himg
          · intro hy
            have hy' := hy
            change
              y ∈ D.func
                ⟨F, Pattern.ofTuple (sumMap e ∘ t)⟩
                (Structure.funcTuple
                  (Pattern.pad (sumMap e ∘ t) h')
                  (Pattern.dummy (sumMap e ∘ t) h')) at hy'
            rw [hp, hargs] at hy'
            rw [← e.map_func ⟨F, Pattern.ofTuple t⟩
              (Structure.funcTuple (Pattern.pad t h)
                (Pattern.dummy t h))] at hy'
            rcases hy' with ⟨x, hx, rfl⟩
            exact ⟨Sum.inr x, hx, rfl⟩
    · have h' : ¬(Pattern.ofTuple (sumMap e ∘ t)).HasMoving :=
        fun ht => h ((Pattern.hasMoving_sumMap e t).1 ht)
      have hr := Pattern.rootTuple_sumMap e t h h'
      ext y
      cases y with
      | inl r =>
          simp [Structure.imageSet, decode, h, h', hr, sumMap]
      | inr y =>
          simp [Structure.imageSet, decode, h, h', hr, sumMap]

@[simp] theorem decodeEmbedding_apply
    (Root : Structure L R)
    {C : Structure (language L R) V}
    {D : Structure (language L R) W}
    (e : Structure.Embedding C D) (x : Sum R V) :
    decodeEmbedding Root e x = sumMap e x := rfl

end StructuralRamsey.Rooted

import PartiteConstruction.Structure.RootedReduction

set_option autoImplicit false

/-! # Functoriality of the rooted reduction

Decoding fixes the root and is functorial in the moving structure.  This is the
bridge needed to transport hereditary classes, free amalgams, embeddings, and
Ramsey arrows through the elimination of constants.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v

variable {L : Language.{u}} {R V W : Type v}

theorem Pattern.not_hasMoving_inl {n : ℕ} (x : Fin n → R) :
    ¬ Pattern.HasMoving (Sum.inl ∘ x : Fin n → Sum R V) := by
  rintro ⟨i, y, h⟩
  exact Sum.noConfusion h

theorem decode_rel_sumFill
    (Root : Structure L R) (C : Structure (language L R) V)
    (S : L.RelSymbol) (p : Pattern (L.relArity S) R)
    (hp : 0 < p.arity) (x : Fin p.arity → V) :
    (decode Root C).rel S (Pattern.sumFill p x) ↔
      C.rel (.base S p hp) x := by
  have hm := Pattern.hasMoving_sumFill p x hp
  simp [decode, hm]

theorem decode_func_sumFill_inl
    (Root : Structure L R) (C : Structure (language L R) V)
    (F : L.FuncSymbol) (p : Pattern (L.funcArity F) R)
    (hp : 0 < p.arity) (x : Fin p.arity → V) (r : R) :
    Sum.inl r ∈ (decode Root C).func F (Pattern.sumFill p x) ↔
      C.rel (.output F p hp r) x := by
  have hm := Pattern.hasMoving_sumFill p x hp
  simp [decode, hm]

theorem decode_func_sumFill_inr
    (Root : Structure L R) (C : Structure (language L R) V)
    (F : L.FuncSymbol) (p : Pattern (L.funcArity F) R)
    (hp : 0 < p.arity) (x : Fin p.arity → V) (y : V) :
    Sum.inr y ∈ (decode Root C).func F (Pattern.sumFill p x) ↔
      y ∈ C.func ⟨F, p, hp⟩ x := by
  have hm := Pattern.hasMoving_sumFill p x hp
  simp [decode, hm]

/-- The fixed root is a full substructure of every decoded moving structure. -/
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

/-- A moving embedding extends by the identity on the fixed root. -/
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
    by_cases h : Pattern.HasMoving t
    · have h' : Pattern.HasMoving (sumMap e ∘ t) :=
        (Pattern.hasMoving_sumMap e t).2 h
      have hp := Pattern.ofTuple_sumMap e t
      have hm := Pattern.movingTuple_sumMap e t
      simp only [decode, dif_pos h, dif_pos h']
      rw [hp, hm]
      exact e.map_rel_iff
        (.base S (Pattern.ofTuple t)
          (Pattern.arity_pos_of_hasMoving t h))
        (Pattern.movingTuple t)
    · have h' : ¬ Pattern.HasMoving (sumMap e ∘ t) :=
        fun ht => h ((Pattern.hasMoving_sumMap e t).1 ht)
      have hr := Pattern.rootTuple_sumMap e t h h'
      simp only [decode, dif_neg h, dif_neg h']
      rw [hr]
  map_func := by
    intro F t
    by_cases h : Pattern.HasMoving t
    · have h' : Pattern.HasMoving (sumMap e ∘ t) :=
        (Pattern.hasMoving_sumMap e t).2 h
      have hp := Pattern.ofTuple_sumMap e t
      have hm := Pattern.movingTuple_sumMap e t
      ext y
      cases y with
      | inl r =>
          simp only [Structure.imageSet, decode, dif_pos h, dif_pos h']
          constructor
          · rintro ⟨z, hz, heq⟩
            cases z with
            | inl s =>
                have hrs : s = r := by
                  simpa [sumMap] using heq
                subst s
                change
                  D.rel
                    (.output F (Pattern.ofTuple (sumMap e ∘ t))
                      (Pattern.arity_pos_of_hasMoving _ h') r)
                    (Pattern.movingTuple (sumMap e ∘ t))
                rw [hp, hm]
                exact
                  (e.map_rel_iff
                    (.output F (Pattern.ofTuple t)
                      (Pattern.arity_pos_of_hasMoving t h) r)
                    (Pattern.movingTuple t)).mpr hz
            | inr z =>
                simp [sumMap] at heq
          · intro hz
            refine ⟨Sum.inl r, ?_, rfl⟩
            change
              C.rel
                (.output F (Pattern.ofTuple t)
                  (Pattern.arity_pos_of_hasMoving t h) r)
                (Pattern.movingTuple t)
            have hz' := hz
            change
              D.rel
                (.output F (Pattern.ofTuple (sumMap e ∘ t))
                  (Pattern.arity_pos_of_hasMoving _ h') r)
                (Pattern.movingTuple (sumMap e ∘ t)) at hz'
            rw [hp, hm] at hz'
            exact
              (e.map_rel_iff
                (.output F (Pattern.ofTuple t)
                  (Pattern.arity_pos_of_hasMoving t h) r)
                (Pattern.movingTuple t)).mp hz'
      | inr y =>
          simp only [Structure.imageSet, decode, dif_pos h, dif_pos h']
          constructor
          · rintro ⟨z, hz, heq⟩
            cases z with
            | inl r =>
                simp [sumMap] at heq
            | inr x =>
                have hex : e x = y := by
                  simpa [sumMap] using heq
                change
                  y ∈ D.func
                    ⟨F, Pattern.ofTuple (sumMap e ∘ t),
                      Pattern.arity_pos_of_hasMoving _ h'⟩
                    (Pattern.movingTuple (sumMap e ∘ t))
                rw [hp, hm]
                have himg :
                    e x ∈ Structure.imageSet e
                      (C.func
                        ⟨F, Pattern.ofTuple t,
                          Pattern.arity_pos_of_hasMoving t h⟩
                        (Pattern.movingTuple t)) :=
                  ⟨x, hz, rfl⟩
                rw [e.map_func
                  ⟨F, Pattern.ofTuple t,
                    Pattern.arity_pos_of_hasMoving t h⟩
                  (Pattern.movingTuple t)] at himg
                rwa [hex] at himg
          · intro hy
            have hy' := hy
            change
              y ∈ D.func
                ⟨F, Pattern.ofTuple (sumMap e ∘ t),
                  Pattern.arity_pos_of_hasMoving _ h'⟩
                (Pattern.movingTuple (sumMap e ∘ t)) at hy'
            rw [hp, hm] at hy'
            rw [← e.map_func
              ⟨F, Pattern.ofTuple t,
                Pattern.arity_pos_of_hasMoving t h⟩
              (Pattern.movingTuple t)] at hy'
            rcases hy' with ⟨x, hx, rfl⟩
            exact ⟨Sum.inr x, hx, rfl⟩
    · have h' : ¬ Pattern.HasMoving (sumMap e ∘ t) :=
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

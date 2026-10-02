import PartiteConstruction.Iterated.LocalTreeLike

/-! # Lifting compatible homomorphism-embeddings across free amalgams

The source and target free amalgams may use different overlap structures.
A compatibility map between the overlaps is enough: the induced map on the
whole source free amalgam is a homomorphism-embedding whenever the two side
maps are homomorphism-embeddings.
-/
namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C G E₂ F₂ T : Type v}
variable {D₁ : RelStructure L H} {A₁ : RelStructure L E}
variable {B₁ : RelStructure L F} {C₁ : RelStructure L C}
variable {D₂ : RelStructure L G} {A₂ : RelStructure L E₂}
variable {B₂ : RelStructure L F₂} {C₂ : RelStructure L T}
variable {sA : Embedding D₁ A₁} {sB : Embedding D₁ B₁}
variable {iA : Embedding A₁ C₁} {iB : Embedding B₁ C₁}
variable {tA : Embedding D₂ A₂} {tB : Embedding D₂ B₂}
variable {jA : Embedding A₂ C₂} {jB : Embedding B₂ C₂}

/-- Candidate output values for a point of the source amalgam. -/
def LiftOutput
    (iA : Embedding A₁ C₁) (iB : Embedding B₁ C₁)
    (jA : Embedding A₂ C₂) (jB : Embedding B₂ C₂)
    (hA : E → E₂) (hB : F → F₂) (z : C) (w : T) : Prop :=
  (∃ a : E, z = iA a ∧ w = jA (hA a)) ∨
  (∃ b : F, z = iB b ∧ w = jB (hB b))

theorem liftOutput_existsUnique
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (z : C) :
    ∃! w : T, LiftOutput iA iB jA jB hA hB z w := by
  classical
  obtain hzA | hzB := hSrc.covers z
  · rcases hzA with ⟨a, rfl⟩
    refine ⟨jA (hA a), Or.inl ⟨a, rfl, rfl⟩, ?_⟩
    intro w hw
    rcases hw with ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩
    · have haa : a = a' := iA.injective ha'
      subst a'
      rfl
    · obtain ⟨d, had, hbd⟩ := (hSrc.overlap a b).mp hb
      subst a
      subst b
      rw [hcompatA d, hcompatB d]
      exact ((hTgt.overlap (tA (q d)) (tB (q d))).mpr
        ⟨q d, rfl, rfl⟩).symm
  · rcases hzB with ⟨b, rfl⟩
    refine ⟨jB (hB b), Or.inr ⟨b, rfl, rfl⟩, ?_⟩
    intro w hw
    rcases hw with ⟨a, ha, rfl⟩ | ⟨b', hb', rfl⟩
    · obtain ⟨d, had, hbd⟩ := (hSrc.overlap a b).mp ha.symm
      subst a
      subst b
      rw [hcompatA d, hcompatB d]
      exact (hTgt.overlap (tA (q d)) (tB (q d))).mpr
        ⟨q d, rfl, rfl⟩
    · have hbb : b = b' := iB.injective hb'
      subst b'
      rfl

noncomputable def liftMap
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d)) :
    C → T :=
  fun z => Classical.choose
    (liftOutput_existsUnique hSrc hTgt q hA hB hcompatA hcompatB z)

theorem liftMap_spec
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (z : C) :
    LiftOutput iA iB jA jB hA hB z
      (liftMap hSrc hTgt q hA hB hcompatA hcompatB z) :=
  (Classical.choose_spec
    (liftOutput_existsUnique hSrc hTgt q hA hB hcompatA hcompatB z)).1

theorem liftMap_left
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (a : E) :
    liftMap hSrc hTgt q hA hB hcompatA hcompatB (iA a) =
      jA (hA a) := by
  let hex := liftOutput_existsUnique hSrc hTgt q hA hB hcompatA hcompatB (iA a)
  exact hex.unique
    (liftMap_spec hSrc hTgt q hA hB hcompatA hcompatB (iA a))
    (Or.inl ⟨a, rfl, rfl⟩)

theorem liftMap_right
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (b : F) :
    liftMap hSrc hTgt q hA hB hcompatA hcompatB (iB b) =
      jB (hB b) := by
  let hex := liftOutput_existsUnique hSrc hTgt q hA hB hcompatA hcompatB (iB b)
  exact hex.unique
    (liftMap_spec hSrc hTgt q hA hB hcompatA hcompatB (iB b))
    (Or.inr ⟨b, rfl, rfl⟩)

/-- Compatible homomorphism-embeddings on the two sides lift through the
source and target free amalgams, even when their overlap domains differ. -/
theorem liftMap_isHomomorphismEmbedding
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hhA : A₁.IsHomomorphismEmbedding A₂ hA)
    (hhB : B₁.IsHomomorphismEmbedding B₂ hB) :
    C₁.IsHomomorphismEmbedding C₂
      (liftMap hSrc hTgt q hA hB hcompatA hcompatB) := by
  classical
  let Fmap := liftMap hSrc hTgt q hA hB hcompatA hcompatB
  apply IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    rcases (hSrc.rel_iff R x).mp hx with hleft | hright
    · rcases hleft with ⟨y, hy, hxy⟩
      have hA₂rel : A₂.rel R (hA ∘ y) := hhA.1 R y hy
      have hC₂rel : C₂.rel R (jA ∘ (hA ∘ y)) :=
        (jA.map_rel_iff R (hA ∘ y)).mpr hA₂rel
      convert hC₂rel using 1
      funext k
      have hxk : x k = iA (y k) := congrFun hxy k
      change liftMap hSrc hTgt q hA hB hcompatA hcompatB (x k) =
        jA (hA (y k))
      rw [hxk]
      exact liftMap_left hSrc hTgt q hA hB hcompatA hcompatB (y k)
    · rcases hright with ⟨y, hy, hxy⟩
      have hB₂rel : B₂.rel R (hB ∘ y) := hhB.1 R y hy
      have hC₂rel : C₂.rel R (jB ∘ (hB ∘ y)) :=
        (jB.map_rel_iff R (hB ∘ y)).mpr hB₂rel
      convert hC₂rel using 1
      funext k
      have hxk : x k = iB (y k) := congrFun hxy k
      change liftMap hSrc hTgt q hA hB hcompatA hcompatB (x k) =
        jB (hB (y k))
      rw [hxk]
      exact liftMap_right hSrc hTgt q hA hB hcompatA hcompatB (y k)
  · intro S hS
    rcases hSrc.irreducible_side S hS with hleft | hright
    · let pre : S → E := fun z => Classical.choose (hleft z)
      have hpre (z : S) : z.1 = iA (pre z) :=
        Classical.choose_spec (hleft z)
      let Rng : Set E := Set.range pre
      have hRng : (A₁.induce Rng).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R, z, k, l, hz, hzk, hzl⟩ := hS hsab
        change C₁.rel R (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R) → E := fun t => pre (z t)
        have heq : Subtype.val ∘ z = iA ∘ y := by
          funext t
          exact hpre (z t)
        rw [heq] at hz
        have hArel := (iA.map_rel_iff R y).mp hz
        let yR : Fin (L.arity R) → Rng :=
          fun t => ⟨y t, ⟨z t, rfl⟩⟩
        refine ⟨R, yR, k, l, hArel, ?_, ?_⟩
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      intro x hx y hy hxy
      let xs : S := ⟨x, hx⟩
      let ys : S := ⟨y, hy⟩
      have hFx :
          Fmap x = jA (hA (pre xs)) := by
        change Fmap xs.1 = _
        rw [hpre xs]
        exact liftMap_left hSrc hTgt q hA hB hcompatA hcompatB (pre xs)
      have hFy :
          Fmap y = jA (hA (pre ys)) := by
        change Fmap ys.1 = _
        rw [hpre ys]
        exact liftMap_left hSrc hTgt q hA hB hcompatA hcompatB (pre ys)
      have hh : hA (pre xs) = hA (pre ys) := by
        apply jA.injective
        rw [← hFx, ← hFy]
        exact hxy
      have hp : pre xs = pre ys :=
        hhA.injOn Rng hRng ⟨xs, rfl⟩ ⟨ys, rfl⟩ hh
      calc
        x = xs.1 := rfl
        _ = iA (pre xs) := hpre xs
        _ = iA (pre ys) := congrArg iA hp
        _ = ys.1 := (hpre ys).symm
        _ = y := rfl
    · let pre : S → F := fun z => Classical.choose (hright z)
      have hpre (z : S) : z.1 = iB (pre z) :=
        Classical.choose_spec (hright z)
      let Rng : Set F := Set.range pre
      have hRng : (B₁.induce Rng).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R, z, k, l, hz, hzk, hzl⟩ := hS hsab
        change C₁.rel R (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R) → F := fun t => pre (z t)
        have heq : Subtype.val ∘ z = iB ∘ y := by
          funext t
          exact hpre (z t)
        rw [heq] at hz
        have hBrel := (iB.map_rel_iff R y).mp hz
        let yR : Fin (L.arity R) → Rng :=
          fun t => ⟨y t, ⟨z t, rfl⟩⟩
        refine ⟨R, yR, k, l, hBrel, ?_, ?_⟩
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      intro x hx y hy hxy
      let xs : S := ⟨x, hx⟩
      let ys : S := ⟨y, hy⟩
      have hFx :
          Fmap x = jB (hB (pre xs)) := by
        change Fmap xs.1 = _
        rw [hpre xs]
        exact liftMap_right hSrc hTgt q hA hB hcompatA hcompatB (pre xs)
      have hFy :
          Fmap y = jB (hB (pre ys)) := by
        change Fmap ys.1 = _
        rw [hpre ys]
        exact liftMap_right hSrc hTgt q hA hB hcompatA hcompatB (pre ys)
      have hh : hB (pre xs) = hB (pre ys) := by
        apply jB.injective
        rw [← hFx, ← hFy]
        exact hxy
      have hp : pre xs = pre ys :=
        hhB.injOn Rng hRng ⟨xs, rfl⟩ ⟨ys, rfl⟩ hh
      calc
        x = xs.1 := rfl
        _ = iB (pre xs) := hpre xs
        _ = iB (pre ys) := congrArg iB hp
        _ = ys.1 := (hpre ys).symm
        _ = y := rfl
  · intro S hS R x hxS htarget
    rcases hSrc.irreducible_side S hS with hleft | hright
    · let pre : S → E := fun z => Classical.choose (hleft z)
      have hpre (z : S) : z.1 = iA (pre z) :=
        Classical.choose_spec (hleft z)
      let Rng : Set E := Set.range pre
      have hRng : (A₁.induce Rng).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R', z, k, l, hz, hzk, hzl⟩ := hS hsab
        change C₁.rel R' (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R') → E := fun t => pre (z t)
        have heq : Subtype.val ∘ z = iA ∘ y := by
          funext t
          exact hpre (z t)
        rw [heq] at hz
        have hArel := (iA.map_rel_iff R' y).mp hz
        let yR : Fin (L.arity R') → Rng :=
          fun t => ⟨y t, ⟨z t, rfl⟩⟩
        refine ⟨R', yR, k, l, hArel, ?_, ?_⟩
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      let xs : Fin (L.arity R) → S := fun k => ⟨x k, hxS k⟩
      let y : Fin (L.arity R) → E := fun k => pre (xs k)
      have hyR : ∀ k, y k ∈ Rng := fun k => ⟨xs k, rfl⟩
      have heqTarget :
          Fmap ∘ x = jA ∘ (hA ∘ y) := by
        funext k
        change Fmap (xs k).1 = jA (hA (y k))
        rw [hpre (xs k)]
        exact liftMap_left hSrc hTgt q hA hB hcompatA hcompatB (y k)
      rw [heqTarget] at htarget
      have hA₂rel : A₂.rel R (hA ∘ y) :=
        (jA.map_rel_iff R (hA ∘ y)).mp htarget
      have hArel := hhA.reflect_rel_on Rng hRng R y hyR hA₂rel
      have heqSource : x = iA ∘ y := by
        funext k
        exact hpre (xs k)
      rw [heqSource]
      exact (iA.map_rel_iff R y).mpr hArel
    · let pre : S → F := fun z => Classical.choose (hright z)
      have hpre (z : S) : z.1 = iB (pre z) :=
        Classical.choose_spec (hright z)
      let Rng : Set F := Set.range pre
      have hRng : (B₁.induce Rng).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R', z, k, l, hz, hzk, hzl⟩ := hS hsab
        change C₁.rel R' (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R') → F := fun t => pre (z t)
        have heq : Subtype.val ∘ z = iB ∘ y := by
          funext t
          exact hpre (z t)
        rw [heq] at hz
        have hBrel := (iB.map_rel_iff R' y).mp hz
        let yR : Fin (L.arity R') → Rng :=
          fun t => ⟨y t, ⟨z t, rfl⟩⟩
        refine ⟨R', yR, k, l, hBrel, ?_, ?_⟩
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      let xs : Fin (L.arity R) → S := fun k => ⟨x k, hxS k⟩
      let y : Fin (L.arity R) → F := fun k => pre (xs k)
      have hyR : ∀ k, y k ∈ Rng := fun k => ⟨xs k, rfl⟩
      have heqTarget :
          Fmap ∘ x = jB ∘ (hB ∘ y) := by
        funext k
        change Fmap (xs k).1 = jB (hB (y k))
        rw [hpre (xs k)]
        exact liftMap_right hSrc hTgt q hA hB hcompatA hcompatB (y k)
      rw [heqTarget] at htarget
      have hB₂rel : B₂.rel R (hB ∘ y) :=
        (jB.map_rel_iff R (hB ∘ y)).mp htarget
      have hBrel := hhB.reflect_rel_on Rng hRng R y hyR hB₂rel
      have heqSource : x = iB ∘ y := by
        funext k
        exact hpre (xs k)
      rw [heqSource]
      exact (iB.map_rel_iff R y).mpr hBrel

end StructuralRamsey.RelStructure.IsFreeAmalgam

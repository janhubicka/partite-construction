import PartiteConstruction.Structure.FreeAmalgam

/-! # Free attachment for structures with set-valued functions

Attach copies of B along a closed substructure B|S to a core D. Relations and
function-value incidences are exactly those inherited from the core or one
attached copy.  Closure of S is essential for the core and copy maps to be full
embeddings when functions are set-valued.
-/
namespace StructuralRamsey.Structure.Attachment

universe u v
variable {L : Language.{u}} {V W I : Type v}
variable (B : Structure L V) (S : Set V) (hS : B.IsClosed S)
variable (D : Structure L W)
variable (f : I → Embedding (B.induce S hS) D)

abbrev Vertex := W ⊕ (I × {x : V // x ∉ S})

noncomputable def copyMap (i : I) (x : V) : Vertex S (W := W) (I := I) := by
  classical
  exact if hx : x ∈ S then .inl (f i ⟨x, hx⟩) else .inr (i, ⟨x, hx⟩)

variable {B S hS D f}

@[simp] theorem copyMap_mem (i : I) (x : V) (hx : x ∈ S) :
    copyMap B S hS D f i x = .inl (f i ⟨x, hx⟩) := by
  classical
  simp [copyMap, hx]

@[simp] theorem copyMap_not_mem (i : I) (x : V) (hx : x ∉ S) :
    copyMap B S hS D f i x = .inr (i, ⟨x, hx⟩) := by
  classical
  simp [copyMap, hx]

theorem mem_of_copyMap_eq_inl {i : I} {x : V} {y : W}
    (h : copyMap B S hS D f i x = .inl y) : x ∈ S := by
  classical
  by_contra hx
  simp [copyMap_not_mem i x hx] at h

theorem copyMap_injective (i : I) :
    Function.Injective (copyMap B S hS D f i) := by
  classical
  intro x y h
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [copyMap_mem i x hx, copyMap_mem i y hy, Sum.inl.injEq] at h
    exact congrArg Subtype.val ((f i).injective h)
  · simp [copyMap_mem i x hx, copyMap_not_mem i y hy] at h
  · simp [copyMap_not_mem i x hx, copyMap_mem i y hy] at h
  · simpa [copyMap_not_mem i x hx, copyMap_not_mem i y hy] using h

theorem index_eq_of_outside {i j : I} {x y : V} (hx : x ∉ S)
    (h : copyMap B S hS D f i x = copyMap B S hS D f j y) : i = j := by
  classical
  by_cases hy : y ∈ S
  · simp [copyMap_not_mem i x hx, copyMap_mem j y hy] at h
  · exact congrArg Prod.fst (Sum.inr.inj (by
      simpa only [copyMap_not_mem i x hx, copyMap_not_mem j y hy] using h))

variable (B S hS D f)

/-- The full free attachment. -/
noncomputable def attach : Structure L (Vertex S (W := W) (I := I)) where
  rel R z :=
    (∃ y, D.rel R y ∧ z = Sum.inl ∘ y) ∨
    (∃ i x, B.rel R x ∧ z = copyMap B S hS D f i ∘ x)
  func F x := {y |
    (∃ a b, b ∈ D.func F a ∧ x = Sum.inl ∘ a ∧ y = .inl b) ∨
    (∃ i a b, b ∈ B.func F a ∧
      x = copyMap B S hS D f i ∘ a ∧
      y = copyMap B S hS D f i b)}

variable {B S hS D f}

theorem core_rel_iff (R : L.RelSymbol) (x : Fin (L.relArity R) → W) :
    (attach B S hS D f).rel R (Sum.inl ∘ x) ↔ D.rel R x := by
  classical
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨i, y, hy, h⟩)
    · have heq : x = y := funext (fun k => Sum.inl.inj (congrFun h k))
      simpa only [heq] using hy
    · have hs : ∀ k, y k ∈ S :=
        fun k => mem_of_copyMap_eq_inl (congrFun h k).symm
      let ys : Fin (L.relArity R) → S := fun k => ⟨y k, hs k⟩
      have heq : x = f i ∘ ys := by
        funext k
        exact Sum.inl.inj (by
          simpa only [Function.comp_apply, copyMap_mem i (y k) (hs k)]
            using congrFun h k)
      rw [heq]
      exact ((f i).map_rel_iff R ys).mpr hy
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

theorem copy_rel_iff (i : I) (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    (attach B S hS D f).rel R (copyMap B S hS D f i ∘ x) ↔ B.rel R x := by
  classical
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨j, y, hy, h⟩)
    · have hs : ∀ k, x k ∈ S :=
        fun k => mem_of_copyMap_eq_inl (congrFun h k)
      let xs : Fin (L.relArity R) → S := fun k => ⟨x k, hs k⟩
      have heq : f i ∘ xs = y := by
        funext k
        exact Sum.inl.inj (by
          simpa only [Function.comp_apply, copyMap_mem i (x k) (hs k)]
            using congrFun h k)
      exact ((f i).map_rel_iff R xs).mp (by simpa only [heq] using hy)
    · by_cases hs : ∀ k, x k ∈ S
      · have ht : ∀ k, y k ∈ S := by
          intro k
          apply mem_of_copyMap_eq_inl (f := f) (i := j)
          exact (congrFun h k).symm.trans (copyMap_mem i (x k) (hs k))
        let xs : Fin (L.relArity R) → S := fun k => ⟨x k, hs k⟩
        let ys : Fin (L.relArity R) → S := fun k => ⟨y k, ht k⟩
        have heq : f i ∘ xs = f j ∘ ys := by
          funext k
          exact Sum.inl.inj (by
            simpa only [Function.comp_apply, copyMap_mem i (x k) (hs k),
              copyMap_mem j (y k) (ht k)] using congrFun h k)
        apply ((f i).map_rel_iff R xs).mp
        rw [heq]
        exact ((f j).map_rel_iff R ys).mpr hy
      · push Not at hs
        obtain ⟨k, hk⟩ := hs
        have hij := index_eq_of_outside hk (congrFun h k)
        subst j
        have heq : x = y :=
          funext (fun k => copyMap_injective i (congrFun h k))
        simpa only [heq] using hy
  · intro hx
    exact Or.inr ⟨i, x, hx, rfl⟩

/-- Function values on a core tuple are exactly the core images. -/
theorem core_func (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → W) :
    Structure.imageSet Sum.inl (D.func F x) =
      (attach B S hS D f).func F (Sum.inl ∘ x) := by
  classical
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Or.inl ⟨x, y, hy, rfl, rfl⟩
  · intro hz
    rcases hz with
      ⟨a, b, hb, hargs, hout⟩ |
      ⟨i, a, b, hb, hargs, hout⟩
    · have ha : a = x := by
        funext k
        exact Sum.inl.inj (congrFun hargs k).symm
      subst a
      exact ⟨b, hb, hout.symm⟩
    · have haS : ∀ k, a k ∈ S := by
        intro k
        apply mem_of_copyMap_eq_inl
        exact (congrFun hargs k).symm
      have hbS : b ∈ S := hS F a haS hb
      let as : Fin (L.funcArity F) → S := fun k => ⟨a k, haS k⟩
      let bs : S := ⟨b, hbS⟩
      have hargEq : f i ∘ as = x := by
        funext k
        apply Sum.inl.inj
        simpa only [Function.comp_apply, copyMap_mem i (a k) (haS k)]
          using (congrFun hargs k).symm
      have himg :
          f i bs ∈ D.func F (f i ∘ as) := by
        have hsrc :
            bs ∈ (B.induce S hS).func F as := hb
        have h :
            f i bs ∈
              Structure.imageSet (f i)
                ((B.induce S hS).func F as) :=
          ⟨bs, hsrc, rfl⟩
        rw [(f i).map_func F as] at h
        exact h
      rw [hargEq] at himg
      refine ⟨f i bs, himg, ?_⟩
      rw [hout, copyMap_mem i b hbS]

/-- Function values on an attached copy tuple are exactly the copy images. -/
theorem copy_func (i : I) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    Structure.imageSet (copyMap B S hS D f i) (B.func F x) =
      (attach B S hS D f).func F (copyMap B S hS D f i ∘ x) := by
  classical
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact Or.inr ⟨i, x, b, hb, rfl, rfl⟩
  · intro hz
    rcases hz with
      ⟨a, b, hb, hargs, hout⟩ |
      ⟨j, a, b, hb, hargs, hout⟩
    · have hxS : ∀ k, x k ∈ S := by
        intro k
        apply mem_of_copyMap_eq_inl
        exact congrFun hargs k
      let xs : Fin (L.funcArity F) → S := fun k => ⟨x k, hxS k⟩
      have hargEq : f i ∘ xs = a := by
        funext k
        exact Sum.inl.inj (by
          simpa only [Function.comp_apply, copyMap_mem i (x k) (hxS k)]
            using congrFun hargs k)
      have hb' : b ∈ D.func F (f i ∘ xs) := by
        rw [hargEq]
        exact hb
      rw [← (f i).map_func F xs] at hb'
      rcases hb' with ⟨c, hc, hcb⟩
      refine ⟨c.1, hc, ?_⟩
      rw [hout, ← hcb, copyMap_mem i c.1 c.2]
    · by_cases hxS : ∀ k, x k ∈ S
      · have haS : ∀ k, a k ∈ S := by
          intro k
          apply mem_of_copyMap_eq_inl (f := f) (i := j)
          exact (congrFun hargs k).symm.trans
            (copyMap_mem i (x k) (hxS k))
        have hbS : b ∈ S := hS F a haS hb
        let xs : Fin (L.funcArity F) → S := fun k => ⟨x k, hxS k⟩
        let as : Fin (L.funcArity F) → S := fun k => ⟨a k, haS k⟩
        let bs : S := ⟨b, hbS⟩
        have hargEq : f i ∘ xs = f j ∘ as := by
          funext k
          exact Sum.inl.inj (by
            simpa only [Function.comp_apply, copyMap_mem i (x k) (hxS k),
              copyMap_mem j (a k) (haS k)] using congrFun hargs k)
        have hjb : f j bs ∈ D.func F (f j ∘ as) := by
          have himg :
              f j bs ∈
                Structure.imageSet (f j)
                  ((B.induce S hS).func F as) :=
            ⟨bs, hb, rfl⟩
          rw [(f j).map_func F as] at himg
          exact himg
        rw [← hargEq, ← (f i).map_func F xs] at hjb
        rcases hjb with ⟨c, hc, hci⟩
        refine ⟨c.1, hc, ?_⟩
        rw [hout, copyMap_mem j b hbS,
          ← hci, copyMap_mem i c.1 c.2]
      · push Not at hxS
        obtain ⟨k, hk⟩ := hxS
        have hij := index_eq_of_outside hk (congrFun hargs k)
        subst j
        have hxa : x = a :=
          funext (fun k => copyMap_injective i (congrFun hargs k))
        subst a
        exact ⟨b, hb, hout.symm⟩

variable (B S hS D f)

noncomputable def coreEmbedding :
    Embedding D (attach B S hS D f) where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel_iff := core_rel_iff
  map_func := core_func

noncomputable def copyEmbedding (i : I) :
    Embedding B (attach B S hS D f) where
  toFun := copyMap B S hS D f i
  injective := copyMap_injective i
  map_rel_iff := copy_rel_iff i
  map_func := copy_func i

theorem copy_extends (i : I) (x : S) :
    copyEmbedding B S hS D f i x.1 =
      coreEmbedding B S hS D f (f i x) :=
  copyMap_mem i x.1 x.2

/-- The canonical full attachment is a free amalgam of the core and any one
attached copy over the overlap. -/
theorem isFreeAmalgam (i : I) :
    IsFreeAmalgam (f i) (Embedding.id (B.induce S hS))
      (coreEmbedding B S hS D f) (copyEmbedding B S hS D f i) := by
  -- This theorem is intentionally stated for one attached copy; the full
  -- multi-copy localization theorem is proved separately.
  constructor
  · intro z
    cases z with
    | inl y => exact Or.inl ⟨y, rfl⟩
    | inr p =>
        rcases p with ⟨j, x⟩
        by_cases hji : j = i
        · subst j
          exact Or.inr ⟨x.1, (copyMap_not_mem i x.1 x.2).symm⟩
        · -- vertices from another copy are not covered by these two sides
          -- and therefore this two-side statement is not valid globally.
          contradiction
  · intro a b
    constructor
    · intro hab
      by_cases hb : b ∈ S
      · refine ⟨⟨b, hb⟩, ?_, rfl⟩
        apply (f i).injective
        exact Sum.inl.inj (by
          simpa only [copyMap_mem i b hb] using hab)
      · simp [copyMap_not_mem i b hb] at hab
    · rintro ⟨d, rfl, rfl⟩
      exact copy_extends B S hS D f i d
  · intro R z
    exact Iff.rfl
  · intro F x y
    exact Iff.rfl

end StructuralRamsey.Structure.Attachment

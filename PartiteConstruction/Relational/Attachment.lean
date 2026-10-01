import PartiteConstruction.Relational.Basic

/-! # Free attachment of copies along an induced substructure

Attach a fresh copy of B for every embedding of a fixed induced substructure
B|S into D. Vertices outside S carry the index of their copy. Relations are
exactly the old relations of D and the images of relations of the copies.
Both the core and every attached copy are induced; no arity-positivity or
nonempty-intersection assumption is needed.
-/
namespace StructuralRamsey.RelStructure.Attachment

universe u v w z
variable {L : RelLanguage.{u}} {V : Type v} {W : Type w} {I : Type z}
variable (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
variable (f : I → Embedding (B.induce S) D)

abbrev Vertex := W ⊕ (I × {x : V // x ∉ S})

noncomputable def copyMap (i : I) (x : V) : Vertex S (W := W) (I := I) := by
  classical
  exact if hx : x ∈ S then .inl (f i ⟨x, hx⟩) else .inr (i, ⟨x, hx⟩)

variable {B S D f}

@[simp] theorem copyMap_mem (i : I) (x : V) (hx : x ∈ S) :
    copyMap B S D f i x = .inl (f i ⟨x, hx⟩) := by
  classical
  simp [copyMap, hx]

@[simp] theorem copyMap_not_mem (i : I) (x : V) (hx : x ∉ S) :
    copyMap B S D f i x = .inr (i, ⟨x, hx⟩) := by
  classical
  simp [copyMap, hx]

theorem mem_of_copyMap_eq_inl {i : I} {x : V} {y : W}
    (h : copyMap B S D f i x = .inl y) : x ∈ S := by
  classical
  by_contra hx
  simp [copyMap_not_mem i x hx] at h

theorem copyMap_injective (i : I) : Function.Injective (copyMap B S D f i) := by
  classical
  intro x y h
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [copyMap_mem i x hx, copyMap_mem i y hy, Sum.inl.injEq] at h
    exact congrArg Subtype.val ((f i).injective h)
  · simp [copyMap_mem i x hx, copyMap_not_mem i y hy] at h
  · simp [copyMap_not_mem i x hx, copyMap_mem i y hy] at h
  · simpa [copyMap_not_mem i x hx, copyMap_not_mem i y hy] using h

theorem index_eq_of_outside {i j : I} {x y : V} (hx : x ∉ S)
    (h : copyMap B S D f i x = copyMap B S D f j y) : i = j := by
  classical
  by_cases hy : y ∈ S
  · simp [copyMap_not_mem i x hx, copyMap_mem j y hy] at h
  · exact congrArg Prod.fst (Sum.inr.inj (by
      simpa only [copyMap_not_mem i x hx, copyMap_not_mem j y hy] using h))

variable (B S D f)

noncomputable def attach : RelStructure L (Vertex S (W := W) (I := I)) where
  rel R z :=
    (∃ y, D.rel R y ∧ z = Sum.inl ∘ y) ∨
    (∃ i x, B.rel R x ∧ z = copyMap B S D f i ∘ x)

variable {B S D f}

theorem core_rel_iff (R : L.Symbol) (x : Fin (L.arity R) → W) :
    (attach B S D f).rel R (Sum.inl ∘ x) ↔ D.rel R x := by
  classical
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨i, y, hy, h⟩)
    · have heq : x = y := funext (fun k => Sum.inl.inj (congrFun h k))
      simpa only [heq] using hy
    · have hs : ∀ k, y k ∈ S := fun k => mem_of_copyMap_eq_inl (congrFun h k).symm
      let ys : Fin (L.arity R) → S := fun k => ⟨y k, hs k⟩
      have heq : x = f i ∘ ys := by
        funext k
        exact Sum.inl.inj (by simpa only [Function.comp_apply, copyMap_mem i (y k) (hs k)] using congrFun h k)
      rw [heq]
      exact ((f i).map_rel_iff R ys).mpr hy
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

theorem copy_rel_iff (i : I) (R : L.Symbol) (x : Fin (L.arity R) → V) :
    (attach B S D f).rel R (copyMap B S D f i ∘ x) ↔ B.rel R x := by
  classical
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨j, y, hy, h⟩)
    · have hs : ∀ k, x k ∈ S := fun k => mem_of_copyMap_eq_inl (congrFun h k)
      let xs : Fin (L.arity R) → S := fun k => ⟨x k, hs k⟩
      have heq : f i ∘ xs = y := by
        funext k
        exact Sum.inl.inj (by simpa only [Function.comp_apply, copyMap_mem i (x k) (hs k)] using congrFun h k)
      exact ((f i).map_rel_iff R xs).mp (by simpa only [heq] using hy)
    · by_cases hs : ∀ k, x k ∈ S
      · have ht : ∀ k, y k ∈ S := by
          intro k
          apply mem_of_copyMap_eq_inl (f := f) (i := j)
          exact (congrFun h k).symm.trans (copyMap_mem i (x k) (hs k))
        let xs : Fin (L.arity R) → S := fun k => ⟨x k, hs k⟩
        let ys : Fin (L.arity R) → S := fun k => ⟨y k, ht k⟩
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
        have heq : x = y := funext (fun k => copyMap_injective i (congrFun h k))
        simpa only [heq] using hy
  · intro hx
    exact Or.inr ⟨i, x, hx, rfl⟩

variable (B S D f)

noncomputable def coreEmbedding : Embedding D (attach B S D f) where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel_iff := core_rel_iff

noncomputable def copyEmbedding (i : I) : Embedding B (attach B S D f) where
  toFun := copyMap B S D f i
  injective := copyMap_injective i
  map_rel_iff := copy_rel_iff i

/-- Every prescribed embedding of B|S extends to a copy of B. -/
theorem copy_extends (i : I) (x : S) :
    copyEmbedding B S D f i x.val = coreEmbedding B S D f (f i x) :=
  copyMap_mem i x.val x.property

end StructuralRamsey.RelStructure.Attachment

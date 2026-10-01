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

/-- Any relation tuple containing a vertex outside the core belongs to the
unique attached copy indexed by that vertex. -/
theorem relation_eq_copy_of_contains_outside
    {R : L.Symbol} {z : Fin (L.arity R) → Vertex S (W := W) (I := I)}
    (hz : (attach B S D f).rel R z) (k : Fin (L.arity R))
    (i : I) (x : {x : V // x ∉ S}) (hk : z k = .inr (i, x)) :
    ∃ y : Fin (L.arity R) → V, B.rel R y ∧
      z = copyMap B S D f i ∘ y := by
  classical
  rcases hz with ⟨y, hy, hcore⟩ | ⟨j, y, hy, hcopy⟩
  · have h := congrFun hcore k
    rw [hk] at h
    simp at h
  · have hcoord := congrFun hcopy k
    rw [hk] at hcoord
    by_cases hmem : y k ∈ S
    · rw [copyMap_mem j (y k) hmem] at hcoord
      simp at hcoord
    · have hp : (j, ⟨y k, hmem⟩) = (i, x) := by
        apply Sum.inr.inj
        simpa only [copyMap_not_mem j (y k) hmem, Function.comp_apply] using hcoord.symm
      have hji : j = i := congrArg Prod.fst hp
      subst j
      exact ⟨y, hy, hcopy⟩

/-- An irreducible substructure of a free attachment lies wholly in the core
or wholly in one attached copy. This is the structural invariant used by the
induced Picture Lemma. -/
theorem irreducible_core_or_copy
    (T : Set (Vertex S (W := W) (I := I)))
    (hT : ((attach B S D f).induce T).Irreducible) :
    (∀ z : T, ∃ y : W, z.1 = .inl y) ∨
      ∃ i : I, ∀ z : T, ∃ x : V, z.1 = copyMap B S D f i x := by
  classical
  by_cases hcore : ∀ z : T, ∃ y : W, z.1 = .inl y
  · exact Or.inl hcore
  · push Not at hcore
    obtain ⟨a, ha⟩ := hcore
    cases hval : a.1 with
    | inl y => exact (ha ⟨y, hval⟩).elim
    | inr ix =>
        let i : I := ix.1
        let x0 : {x : V // x ∉ S} := ix.2
        refine Or.inr ⟨i, ?_⟩
        intro b
        by_cases hba : b = a
        · subst b
          refine ⟨x0.1, ?_⟩
          change a.1 = copyMap B S D f i x0.1
          rw [hval]
          symm
          exact copyMap_not_mem i x0.1 x0.2
        · have hab : a ≠ b := Ne.symm hba
          obtain ⟨R, z, k, l, hz, hza, hzb⟩ := hT hab
          change (attach B S D f).rel R (Subtype.val ∘ z) at hz
          have hk : (Subtype.val ∘ z) k = .inr (i, x0) := by
            change (z k).1 = .inr (i, x0)
            rw [hza]
            exact hval
          obtain ⟨y, hy, heq⟩ :=
            relation_eq_copy_of_contains_outside hz k i x0 hk
          refine ⟨y l, ?_⟩
          have hl := congrFun heq l
          change (z l).1 = copyMap B S D f i (y l) at hl
          rw [hzb] at hl
          exact hl

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

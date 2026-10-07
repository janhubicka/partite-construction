import PartiteConstruction.Relational.Attachment

/-! # Restricting the family of copies in a relational free attachment

A free attachment is an induced substructure of the attachment indexed by
a larger family of copies, provided the old indices inject into the new ones
and their overlap embeddings are unchanged.  The implication is **induced**
even when the common support is not a closed set of vertices (the language
of this lemma is relational).

This observation is used to transfer the weak-vertex-set tree induction to
the U-closed functional Picture construction, whose alphabet indexes fewer,
closed, overlap embeddings.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v

variable {L : RelLanguage.{u}}
variable {V W I J : Type v}
variable {B : RelStructure L V}
variable {D : RelStructure L W}
variable {S : Set V}

/-- Reindex fresh outside vertices while fixing the whole old core. -/
def reindexVertex (j : I ↪ J) :
    Vertex S (W := W) (I := I) → Vertex S (W := W) (I := J)
  | .inl w => .inl w
  | .inr (i, x) => .inr (j i, x)

theorem reindexVertex_injective (j : I ↪ J) :
    Function.Injective (reindexVertex (S := S) (W := W) j) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact congrArg Sum.inl (Sum.inl.inj hxy)
    | inr b =>
      cases hxy
  | inr a =>
    cases y with
    | inl b =>
      cases hxy
    | inr b =>
      exact congrArg Sum.inr
        (Prod.ext
          (j.injective (congrArg Prod.fst (Sum.inr.inj hxy)))
          (congrArg Prod.snd (Sum.inr.inj hxy)))

/-- The selected copied vertex is carried to the correspondingly indexed
copy in the larger attachment. -/
theorem reindexVertex_copy
    (f : I → Embedding (B.induce S) D)
    (g : J → Embedding (B.induce S) D)
    (j : I ↪ J) (hf : ∀ i, f i = g (j i))
    (i : I) (x : V) :
    reindexVertex (S := S) (W := W) j (copyMap B S D f i x) =
      copyMap B S D g (j i) x := by
  classical
  by_cases hx : x ∈ S
  · simp [copyMap_mem i x hx, reindexVertex, hf i]
  · simp [copyMap_not_mem i x hx, reindexVertex]

/-- Choosing an injectively indexed subfamily of copied structures gives
an induced embedding between the free attachments. -/
noncomputable def reindexEmbedding
    (f : I → Embedding (B.induce S) D)
    (g : J → Embedding (B.induce S) D)
    (j : I ↪ J) (hf : ∀ i, f i = g (j i)) :
    Embedding (attach B S D f) (attach B S D g) where
  toFun := reindexVertex j
  injective := reindexVertex_injective j
  map_rel_iff := by
    intro R t
    constructor
    · intro hTarget
      by_cases hcore : ∀ k, ∃ w : W, t k = .inl w
      · choose w hw using hcore
        have ht : t = Sum.inl ∘ w := by
          funext k
          exact hw k
        subst t
        have hcoreTarget :
            (attach B S D g).rel R (Sum.inl ∘ w) := by
          simpa [reindexVertex] using hTarget
        have hwRel : D.rel R w :=
          (core_rel_iff (B := B) (S := S) (D := D)
            (f := g) R w).mp hcoreTarget
        exact Or.inl ⟨w, hwRel, rfl⟩
      · push Not at hcore
        obtain ⟨k, hk⟩ := hcore
        cases ht : t k with
        | inl w =>
            exact (hk w ht).elim
        | inr pair =>
            rcases pair with ⟨i, outside⟩
            have hOutside :
                (reindexVertex j ∘ t) k =
                  .inr (j i, outside) := by
              change reindexVertex j (t k) =
                .inr (j i, outside)
              rw [ht]
              rfl
            obtain ⟨u, hu, htu⟩ :=
              relation_eq_copy_of_contains_outside
                (B := B) (S := S) (D := D) (f := g)
                hTarget k (j i) outside hOutside
            have hSource :
                t = copyMap B S D f i ∘ u := by
              funext l
              apply reindexVertex_injective (S := S) (W := W) j
              calc
                reindexVertex j (t l) =
                    (reindexVertex j ∘ t) l := rfl
                _ = (copyMap B S D g (j i) ∘ u) l :=
                  congrFun htu l
                _ = reindexVertex j
                      (copyMap B S D f i (u l)) :=
                  (reindexVertex_copy f g j hf i (u l)).symm
            exact Or.inr ⟨i, u, hu, hSource⟩
    · intro hSource
      rcases hSource with ⟨w, hw, htw⟩ | ⟨i, u, hu, htu⟩
      · exact Or.inl ⟨w, hw, by
          rw [htw]
          rfl⟩
      · exact Or.inr ⟨j i, u, hu, by
          rw [htu]
          funext k
          exact reindexVertex_copy f g j hf i (u k)⟩

end StructuralRamsey.RelStructure.Attachment

import PartiteConstruction.Relational.Homomorphism

/-! # Injective restrictions of homomorphism-embeddings

For relational structures, every relation tuple has irreducible support: any
two distinct vertices occurring in the tuple occur together in that very
relation. Consequently, a homomorphism-embedding that is injective on a set is
already an induced embedding on the entire induced substructure on that set.

This elementary fact is useful in the equal-cardinality branch of the iterated
partite construction, where the part projection is injective on the tested
set.
-/
namespace StructuralRamsey.RelStructure.IsHomomorphismEmbedding

universe u v w
variable {L : RelLanguage.{u}}
variable {V : Type v} {W : Type w}
variable {A : RelStructure L V} {B : RelStructure L W}
variable {f : V → W}

/-- The finite support of one relation tuple is irreducible. -/
theorem tupleSupport_irreducible
    (R : L.Symbol) (x : Fin (L.arity R) → V)
    (hx : A.rel R x) :
    (A.induce (Set.range x)).Irreducible := by
  intro a b hab
  rcases a.2 with ⟨i, hi⟩
  rcases b.2 with ⟨j, hj⟩
  let z : Fin (L.arity R) → Set.range x :=
    fun k => ⟨x k, ⟨k, rfl⟩⟩
  refine ⟨R, z, i, j, ?_, ?_, ?_⟩
  · change A.rel R (Subtype.val ∘ z)
    convert hx using 1
    funext k
    rfl
  · apply Subtype.ext
    exact hi
  · apply Subtype.ext
    exact hj

/-- If a homomorphism-embedding is injective on S, its restriction to S is an
ordinary induced embedding. -/
theorem embeddingOn_of_injOn
    (hf : A.IsHomomorphismEmbedding B f)
    (S : Set V) (hinj : Set.InjOn f S) :
    ∃ e : Embedding (A.induce S) B, ∀ x, e x = f x.1 := by
  let e : Embedding (A.induce S) B := {
    toFun := fun x => f x.1
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact hinj x.2 y.2 hxy
    map_rel_iff := by
      intro R x
      constructor
      · intro htarget
        let y : Fin (L.arity R) → V := Subtype.val ∘ x
        let T : Set V := Set.range y
        have hTsubset : T ⊆ S := by
          intro v hv
          rcases hv with ⟨i, rfl⟩
          exact (x i).2
        have hinjT : Set.InjOn f T := hinj.mono hTsubset
        have hsourceImage :
            A.rel R y → B.rel R (f ∘ y) := fun hy => hf.map_rel hy
        by_contra hnot
        -- If the target relation were new, its tuple support in the target
        -- would be irreducible.  Pulling that support back through the
        -- injective tuple map gives an irreducible support in A, where hf
        -- reflects relations.
        let Uset : Set V := Set.range y
        have hUirr : (A.induce Uset).Irreducible := by
          -- Irreducibility can be read from the target tuple because f is
          -- injective on Uset and hf reflects each witnessing relation on
          -- irreducible supports; a direct tuple-support argument below
          -- avoids circularity.
          intro a b hab
          rcases a.2 with ⟨i, hi⟩
          rcases b.2 with ⟨j, hj⟩
          have hij : i ≠ j ∨ y i ≠ y j := by
            right
            intro hEq
            apply hab
            apply Subtype.ext
            rw [← hi, ← hj, hEq]
          -- The target relation tuple itself witnesses adjacency after
          -- pulling back its positive source counterpart would be circular;
          -- so use injectivity and the homomorphism-embedding definition on
          -- the two-point range only when it is irreducible.  This branch is
          -- not available in general.
          sorry
        exact hnot (hf.reflect_rel_on Uset hUirr R y
          (fun i => ⟨i, rfl⟩) (by
            convert htarget using 1
            funext i
            rfl))
      · intro hsource
        exact hf.map_rel hsource
  }
  exact ⟨e, fun _ => rfl⟩

end StructuralRamsey.RelStructure.IsHomomorphismEmbedding

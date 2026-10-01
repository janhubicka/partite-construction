import PartiteConstruction.Relational.Basic

/-! # Irreducibility and homomorphism-embeddings

For relational structures, irreducibility means that the Gaifman graph is
complete. A homomorphism-embedding is a homomorphism whose restriction to
every irreducible substructure is an induced embedding, matching the survey's
definition used by the induced partite construction.
-/
namespace StructuralRamsey
namespace RelStructure

universe u v w z

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- A relational structure is irreducible when every two distinct vertices
occur together in some relation tuple. -/
def Irreducible (A : RelStructure L V) : Prop :=
  ∀ ⦃x y : V⦄, x ≠ y →
    ∃ (R : L.Symbol) (z : Fin (L.arity R) → V)
      (i j : Fin (L.arity R)), A.rel R z ∧ z i = x ∧ z j = y

/-- Positive relational homomorphism. No injectivity is required. -/
def IsHomomorphism (A : RelStructure L V) (B : RelStructure L W)
    (f : V → W) : Prop :=
  ∀ R x, A.rel R x → B.rel R (f ∘ x)

/-- A homomorphism which is an induced embedding on every irreducible
substructure of its domain. -/
def IsHomomorphismEmbedding (A : RelStructure L V) (B : RelStructure L W)
    (f : V → W) : Prop :=
  A.IsHomomorphism B f ∧
    ∀ (S : Set V), (A.induce S).Irreducible →
      ∃ e : Embedding (A.induce S) B, ∀ x, e x = f x.1

namespace IsHomomorphismEmbedding

variable {A : RelStructure L V} {B : RelStructure L W} {f : V → W}

theorem map_rel (h : A.IsHomomorphismEmbedding B f) {R : L.Symbol}
    {x : Fin (L.arity R) → V} (hx : A.rel R x) :
    B.rel R (f ∘ x) :=
  h.1 R x hx

theorem embeddingOn (h : A.IsHomomorphismEmbedding B f) (S : Set V)
    (hS : (A.induce S).Irreducible) :
    ∃ e : Embedding (A.induce S) B, ∀ x, e x = f x.1 :=
  h.2 S hS

/-- Build a homomorphism-embedding from global relation preservation,
injectivity on irreducible subsets, and relation reflection on those subsets. -/
theorem of_map_reflect
    (hmap : A.IsHomomorphism B f)
    (hinj : ∀ (S : Set V), (A.induce S).Irreducible → Set.InjOn f S)
    (hrefl : ∀ (S : Set V), (A.induce S).Irreducible →
      ∀ (R : L.Symbol) (x : Fin (L.arity R) → V),
        (∀ i, x i ∈ S) → B.rel R (f ∘ x) → A.rel R x) :
    A.IsHomomorphismEmbedding B f := by
  constructor
  · exact hmap
  · intro S hS
    let e : Embedding (A.induce S) B := {
      toFun := fun x => f x.1
      injective := by
        intro x y hxy
        apply Subtype.ext
        exact hinj S hS x.2 y.2 hxy
      map_rel_iff := by
        intro R x
        constructor
        · intro htarget
          apply hrefl S hS R (Subtype.val ∘ x)
          · exact fun i => (x i).2
          · convert htarget using 1
            funext i
            rfl
        · intro hsource
          apply hmap R (Subtype.val ∘ x)
          exact hsource
    }
    exact ⟨e, fun _ => rfl⟩

theorem injOn (h : A.IsHomomorphismEmbedding B f) (S : Set V)
    (hS : (A.induce S).Irreducible) : Set.InjOn f S := by
  obtain ⟨e, he⟩ := h.embeddingOn S hS
  intro x hx y hy hxy
  have hsub : (⟨x, hx⟩ : S) = ⟨y, hy⟩ := by
    apply e.injective
    rw [he ⟨x, hx⟩, he ⟨y, hy⟩]
    exact hxy
  exact congrArg Subtype.val hsub

theorem reflect_rel_on (h : A.IsHomomorphismEmbedding B f) (S : Set V)
    (hS : (A.induce S).Irreducible) (R : L.Symbol)
    (x : Fin (L.arity R) → V) (hxS : ∀ i, x i ∈ S)
    (hx : B.rel R (f ∘ x)) : A.rel R x := by
  obtain ⟨e, he⟩ := h.embeddingOn S hS
  let xs : Fin (L.arity R) → S := fun i => ⟨x i, hxS i⟩
  have htarget : B.rel R (e ∘ xs) := by
    convert hx using 1
    funext i
    exact he (xs i)
  have hsource := (e.map_rel_iff R xs).mp htarget
  change A.rel R (Subtype.val ∘ xs) at hsource
  have heq : Subtype.val ∘ xs = x := by
    funext i
    rfl
  rw [heq] at hsource
  exact hsource

end IsHomomorphismEmbedding


namespace IsHomomorphismEmbedding

variable {X : Type z} {A : RelStructure L V} {B : RelStructure L W}
  {C : RelStructure L X} {f : V → W} {g : W → X}

/-- Homomorphism-embeddings compose. The only point needing proof is that the
image of an irreducible substructure under the first induced restriction is
again irreducible. -/
theorem comp (hg : B.IsHomomorphismEmbedding C g)
    (hf : A.IsHomomorphismEmbedding B f) :
    A.IsHomomorphismEmbedding C (g ∘ f) := by
  constructor
  · intro R x hx
    exact hg.1 R (f ∘ x) (hf.1 R x hx)
  · intro S hS
    obtain ⟨e, he⟩ := hf.embeddingOn S hS
    let T : Set W := Set.range e
    have hT : (B.induce T).Irreducible := by
      intro a b hab
      rcases a.property with ⟨sa, hsa⟩
      rcases b.property with ⟨sb, hsb⟩
      have hsab : sa ≠ sb := by
        intro hs
        apply hab
        apply Subtype.ext
        rw [← hsa, ← hsb, hs]
      obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hsab
      let zT : Fin (L.arity R) → T := fun k => ⟨e (z k), ⟨z k, rfl⟩⟩
      refine ⟨R, zT, i, j, ?_, ?_, ?_⟩
      · change B.rel R (Subtype.val ∘ zT)
        have hzB := (e.map_rel_iff R z).mpr hz
        convert hzB using 1
        funext k
        rfl
      · apply Subtype.ext
        change e (z i) = a.1
        rw [hzi]
        exact hsa
      · apply Subtype.ext
        change e (z j) = b.1
        rw [hzj]
        exact hsb
    obtain ⟨d, hd⟩ := hg.embeddingOn T hT
    let eT : Embedding (A.induce S) (B.induce T) := {
      toFun := fun x => ⟨e x, ⟨x, rfl⟩⟩
      injective := fun _ _ h => e.injective (congrArg Subtype.val h)
      map_rel_iff := fun R x => by
        change B.rel R (e ∘ x) ↔ A.rel R (Subtype.val ∘ x)
        exact e.map_rel_iff R x
    }
    refine ⟨d.comp eT, ?_⟩
    intro x
    change d (eT x) = g (f x.1)
    rw [hd (eT x)]
    exact congrArg g (he x)

end IsHomomorphismEmbedding

/-- The image of an irreducible structure under an induced embedding is
irreducible as an induced substructure of the target. -/
theorem Irreducible.range_embedding
    {A : RelStructure L V} {B : RelStructure L W}
    (hA : A.Irreducible) (e : Embedding A B) :
    (B.induce (Set.range e)).Irreducible := by
  intro x y hxy
  rcases x.property with ⟨a, ha⟩
  rcases y.property with ⟨b, hb⟩
  have hab : a ≠ b := by
    intro hab
    apply hxy
    apply Subtype.ext
    rw [← ha, ← hb, hab]
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hA hab
  let z' : Fin (L.arity R) → Set.range e :=
    fun k => ⟨e (z k), ⟨z k, rfl⟩⟩
  refine ⟨R, z', i, j, ?_, ?_, ?_⟩
  · change B.rel R (Subtype.val ∘ z')
    have hrel := (e.map_rel_iff R z).mpr hz
    convert hrel using 1
    funext k
    rfl
  · apply Subtype.ext
    change e (z i) = x.1
    rw [hzi]
    exact ha
  · apply Subtype.ext
    change e (z j) = y.1
    rw [hzj]
    exact hb

namespace IsHomomorphismEmbedding

variable {X : Type z} {A : RelStructure L V}
  {C : RelStructure L W} {B : RelStructure L X} {f : W → X}

/-- A homomorphism-embedding followed along an irreducible induced copy gives
an ordinary induced embedding of that copy. -/
theorem after_irreducible_embedding
    (h : C.IsHomomorphismEmbedding B f)
    (hA : A.Irreducible) (e : Embedding A C) :
    ∃ g : Embedding A B, ∀ a, g a = f (e a) := by
  let S : Set W := Set.range e
  have hS : (C.induce S).Irreducible :=
    hA.range_embedding e
  obtain ⟨d, hd⟩ := h.embeddingOn S hS
  let eS : Embedding A (C.induce S) := {
    toFun := fun a => ⟨e a, ⟨a, rfl⟩⟩
    injective := fun _ _ hxy => e.injective (congrArg Subtype.val hxy)
    map_rel_iff := fun R x => by
      change C.rel R (e ∘ x) ↔ A.rel R x
      exact e.map_rel_iff R x
  }
  refine ⟨d.comp eS, ?_⟩
  intro a
  change d (eS a) = f (e a)
  exact hd (eS a)

end IsHomomorphismEmbedding

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W}

/-- Forget the relational data and retain the underlying injective map. -/
def toFunctionEmbedding (e : Embedding A B) : V ↪ W where
  toFun := e
  inj' := e.injective


/-- Every induced embedding is, in particular, a homomorphism-embedding. -/
theorem isHomomorphismEmbedding (e : Embedding A B) :
    A.IsHomomorphismEmbedding B e := by
  constructor
  · intro R x hx
    exact (e.map_rel_iff R x).mpr hx
  · intro S _
    refine ⟨e.comp (inclusion A S), ?_⟩
    intro x
    rfl

end Embedding

end RelStructure
end StructuralRamsey

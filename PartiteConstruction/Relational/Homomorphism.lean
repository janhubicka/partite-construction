import PartiteConstruction.Relational.Basic

/-! # Irreducibility and homomorphism-embeddings

For relational structures, irreducibility means that the Gaifman graph is
complete. A homomorphism-embedding is a homomorphism whose restriction to
every irreducible substructure is an induced embedding, matching the survey's
definition used by the induced partite construction.
-/
namespace StructuralRamsey
namespace RelStructure

universe u v w

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
  simpa [RelStructure.induce, xs] using hsource

end IsHomomorphismEmbedding

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W}

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

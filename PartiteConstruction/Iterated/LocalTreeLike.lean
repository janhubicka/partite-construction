import PartiteConstruction.Relational.Homomorphism

/-! # Free amalgams, tree amalgams, and local tree-likeness

Relational versions of the notions used in the iterated partite construction.
The definitions are deliberately explicit about embeddings and relation
reflection so later proofs can reuse them without informal identifications.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X Y : Type v}

/-- Isomorphism of relational structures. -/
structure Iso (A : RelStructure L V) (B : RelStructure L W) where
  toEquiv : V ≃ W
  map_rel_iff : ∀ R x, B.rel R (toEquiv ∘ x) ↔ A.rel R x

namespace Iso

def refl (A : RelStructure L V) : Iso A A where
  toEquiv := Equiv.refl V
  map_rel_iff := fun _ _ => Iff.rfl

end Iso

/-- Every induced substructure is irreducible.  Ordered relational
structures with a complete binary order relation satisfy this condition, and
it is exactly what makes arbitrary overlaps inside an `A`-copy visible to a
homomorphism-embedding as induced substructures. -/
def HereditarilyIrreducible (A : RelStructure L U) : Prop :=
  ∀ S : Set U, (A.induce S).Irreducible

theorem HereditarilyIrreducible.irreducible
    {A : RelStructure L U} (hA : HereditarilyIrreducible A) :
    A.Irreducible := by
  intro x y hxy
  let xu : (Set.univ : Set U) := ⟨x, Set.mem_univ x⟩
  let yu : (Set.univ : Set U) := ⟨y, Set.mem_univ y⟩
  have hxu : xu ≠ yu := by
    intro h
    exact hxy (congrArg Subtype.val h)
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ :=
    hA (Set.univ : Set U) hxu
  change A.rel R (Subtype.val ∘ z) at hz
  exact ⟨R, Subtype.val ∘ z, i, j, hz,
    congrArg Subtype.val hzi, congrArg Subtype.val hzj⟩

/-- Any structure embedding into a hereditarily irreducible structure is
irreducible. -/
theorem HereditarilyIrreducible.of_embedding
    {A : RelStructure L U} {D : RelStructure L V}
    (hA : HereditarilyIrreducible A) (e : Embedding D A) :
    D.Irreducible := by
  let S : Set U := Set.range e
  have hS : (A.induce S).Irreducible := hA S
  intro x y hxy
  let xs : S := ⟨e x, ⟨x, rfl⟩⟩
  let ys : S := ⟨e y, ⟨y, rfl⟩⟩
  have hxsys : xs ≠ ys := by
    intro h
    apply hxy
    apply e.injective
    exact congrArg Subtype.val h
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxsys
  let q : Fin (L.arity R) → V :=
    fun k => Classical.choose (z k).property
  have hq (k : Fin (L.arity R)) : e (q k) = (z k).1 :=
    Classical.choose_spec (z k).property
  have hAz : A.rel R (e ∘ q) := by
    change A.rel R (Subtype.val ∘ z) at hz
    convert hz using 1
    funext k
    simpa [Function.comp_apply] using hq k
  have hDz : D.rel R q := (e.map_rel_iff R q).mp hAz
  have hqi : q i = x := by
    apply e.injective
    calc
      e (q i) = (z i).1 := hq i
      _ = xs.1 := congrArg Subtype.val hzi
      _ = e x := rfl
  have hqj : q j = y := by
    apply e.injective
    calc
      e (q j) = (z j).1 := hq j
      _ = ys.1 := congrArg Subtype.val hzj
      _ = e y := rfl
  exact ⟨R, q, i, j, hDz, hqi, hqj⟩

/-- The image of an embedding is contained in some irreducible substructure. -/
def Embedding.ContainedInIrreducible
    {A : RelStructure L U} {B : RelStructure L V}
    (f : Embedding A B) : Prop :=
  ∃ S : Set V, (B.induce S).Irreducible ∧ ∀ x : U, f x ∈ S

/-- An embedded substructure whose image lies inside an embedded copy of an
irreducible structure satisfies the gluing-side condition. -/
theorem Embedding.containedInIrreducible_of_range_subset
    {D : RelStructure L U} {A : RelStructure L V}
    {T : RelStructure L W}
    (hA : A.Irreducible) (α : Embedding A T) (g : Embedding D T)
    (h : ∀ d, ∃ a, g d = α a) :
    g.ContainedInIrreducible := by
  let S : Set W := Set.range α
  refine ⟨S, hA.range_embedding α, ?_⟩
  intro d
  obtain ⟨a, ha⟩ := h d
  exact ⟨a, ha.symm⟩


/-- Under hereditary irreducibility, a homomorphism-embedding is an
ordinary embedding on the image of every embedded substructure of `A`. -/
theorem IsHomomorphismEmbedding.on_substructure_of_hereditarilyIrreducible
    {A : RelStructure L U} {C : RelStructure L V} {T : RelStructure L W}
    (hA : HereditarilyIrreducible A) (S : Set U)
    (e : Embedding (A.induce S) C)
    {f : V → W} (hf : C.IsHomomorphismEmbedding T f) :
    ∃ g : Embedding (A.induce S) T, ∀ x, g x = f (e x) := by
  exact hf.after_irreducible_embedding (hA S) e

/-- A concrete relational structure is the free amalgam of `A` and `B`
over `D` when it is covered by induced copies of the two sides, those copies
intersect exactly in the prescribed common image, and every relation tuple
comes wholly from one side. -/
structure IsFreeAmalgam
    {D : RelStructure L U} {A : RelStructure L V}
    {B : RelStructure L W} {C : RelStructure L X}
    (fA : Embedding D A) (fB : Embedding D B)
    (iA : Embedding A C) (iB : Embedding B C) : Prop where
  covers : ∀ z : X, (∃ a : V, z = iA a) ∨ (∃ b : W, z = iB b)
  overlap : ∀ a : V, ∀ b : W,
    iA a = iB b ↔ ∃ d : U, a = fA d ∧ b = fB d
  rel_iff : ∀ R z,
    C.rel R z ↔
      (∃ x : Fin (L.arity R) → V, A.rel R x ∧ z = iA ∘ x) ∨
      (∃ y : Fin (L.arity R) → W, B.rel R y ∧ z = iB ∘ y)

/-- Tree amalgams of copies of a fixed relational structure, following the
survey definition.  Every gluing takes place over a substructure whose image
on each side lies inside an irreducible substructure. -/
inductive TreeAmalgam (Base : RelStructure L V) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W}
      (h : Iso Base T) : TreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : RelStructure L W₁} {T₂ : RelStructure L W₂}
      {D : RelStructure L Z} {T : RelStructure L W}
      (h₁ : TreeAmalgam Base W₁ T₁)
      (h₂ : TreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (hc₁ : f₁.ContainedInIrreducible)
      (hc₂ : f₂.ContainedInIrreducible)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      TreeAmalgam Base W T

/-- Relational formalization of the survey's `(A,B,n)`-local tree-likeness.
For every induced substructure on at most `n` vertices there is a
homomorphism-embedding into a tree amalgam of copies of `B`, and every
`A`-copy meets that small substructure inside some `A`-copy of the target. -/
def LocallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T,
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a'


namespace LocallyTreeLike

variable {A : RelStructure L U} {B : RelStructure L V}
  {C : RelStructure L W} {m n : ℕ}

/-- Local tree-likeness is monotone in the size bound. -/
theorem mono (h : LocallyTreeLike A B C n) (hmn : m ≤ n) :
    LocallyTreeLike A B C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- If `C` homomorphism-embeds into irreducible `A`, and `A` embeds into
`B`, then `C` is locally tree-like at every scale, witnessed by the
one-copy tree amalgam `B`. -/
theorem of_homEmbedding_to_base
    (hA : A.Irreducible) (eAB : Embedding A B)
    (p : W → U) (hp : C.IsHomomorphismEmbedding A p) (n : ℕ) :
    LocallyTreeLike A B C n := by
  intro S _
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B), ?_⟩
  let f : ↥(↑S : Set W) → V := fun x => eAB (p x.1)
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (RelStructure.inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hRestrict :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding A
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding B f := by
    change (C.induce (↑S : Set W)).IsHomomorphismEmbedding B
      (eAB ∘ (p ∘ Subtype.val))
    exact eAB.isHomomorphismEmbedding.comp hRestrict
  refine ⟨f, hf, ?_⟩
  intro α
  obtain ⟨g, hg⟩ := hp.after_irreducible_embedding hA α
  let α' : Embedding A B := eAB.comp g
  refine ⟨α', ?_⟩
  intro a ha
  refine ⟨a, ?_⟩
  change eAB (p (α a)) = eAB (g a)
  exact congrArg eAB (hg a).symm

end LocallyTreeLike

end StructuralRamsey.RelStructure

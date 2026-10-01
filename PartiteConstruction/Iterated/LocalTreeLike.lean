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

/-- The image of an embedding is contained in some irreducible substructure. -/
def Embedding.ContainedInIrreducible
    {A : RelStructure L U} {B : RelStructure L V}
    (f : Embedding A B) : Prop :=
  ∃ S : Set V, (B.induce S).Irreducible ∧ ∀ x : U, f x ∈ S

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

end StructuralRamsey.RelStructure

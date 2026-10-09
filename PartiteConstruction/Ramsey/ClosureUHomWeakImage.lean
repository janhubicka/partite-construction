import PartiteConstruction.Ramsey.ClosureUIrreducible2019

/-! # Exact weak codomain images of U-homomorphism-embeddings

A relational U-homomorphism-embedding can be regarded as a map into any
induced target containing its range.  This includes the *exact* range
itself: it is not generally a U-substructure, and taking its U-closure
would destroy the tested vertex bound.

This is a codomain statement only.  Restriction of a U-homomorphism-
embedding to an arbitrary weak *source* restriction is not justified:
a previously missing root output may make a new small source
U-irreducible.  Because Definition 2.15 tests ALL U-irreducible
substructures, such new tests cannot be dismissed as non-U-closed.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {U V : Type v}
variable {rules : ClosureDescription L}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {f : U → V}

namespace IsUHomomorphismEmbedding

/-- Restrict the *target* to an induced vertex set containing the map
range.  No U-closedness of this target set is required. -/
theorem codRestrict
    (h : IsUHomomorphismEmbedding rules A B f)
    (S : Set V) (hS : ∀ a : U, f a ∈ S) :
    IsUHomomorphismEmbedding rules A (B.induce S)
      (fun a : U => (⟨f a, hS a⟩ : S)) := by
  constructor
  · intro R x hx
    change B.rel R (f ∘ x)
    exact h.map_rel hx
  · intro T hTUIrred
    obtain ⟨e, he⟩ := h.embeddingOn T hTUIrred
    let eS : Embedding (A.induce T) (B.induce S) := {
      toFun := fun x => ⟨e x, by
        rw [he x]
        exact hS x.1⟩
      injective := by
        intro x y hxy
        apply e.injective
        exact congrArg Subtype.val hxy
      map_rel_iff := by
        intro R x
        change B.rel R (e ∘ x) ↔
          A.rel R (Subtype.val ∘ x)
        exact e.map_rel_iff R x
    }
    refine ⟨eS, ?_⟩
    intro x
    apply Subtype.ext
    exact he x

/-- The 2019 projected image is the *weak induced* structure on the
exact vertex range.  It is never enlarged to the U-generated hull. -/
theorem weakImage
    (h : IsUHomomorphismEmbedding rules A B f) :
    IsUHomomorphismEmbedding rules A (B.induce (Set.range f))
      (fun a : U => (⟨f a, ⟨a, rfl⟩⟩ : Set.range f)) :=
  h.codRestrict (Set.range f) (fun a => ⟨a, rfl⟩)

end IsUHomomorphismEmbedding

end StructuralRamsey.RelStructure

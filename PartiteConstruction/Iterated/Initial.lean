import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Partite.InducedInitial

/-! # The initial picture is locally tree-like

A disjoint union of copies of `B` homomorphism-embeds back to `B` by
forgetting the copy index.  Irreducible substructures lie in a single copy, so
this map is a homomorphism-embedding.  Consequently the initial picture is
`(A,B,n)`-locally tree-like for every `n` whenever `A` is irreducible.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P I : Type v}

/-- Forgetting the copy index in a disjoint-union initial picture is a
homomorphism-embedding back to the copied structure. -/
theorem initial_fold_isHomomorphismEmbedding
    (B : RelStructure L V) (β : I → V ↪ P) [Nonempty I] :
    (Partite.Initial.picture B β).toRelStructure.IsHomomorphismEmbedding
      B Prod.snd := by
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    rcases hx with ⟨i, y, hy, hxy⟩
    have heq : Prod.snd ∘ x = y := by
      funext k
      have h := congrFun hxy k
      exact congrArg Prod.snd h
    rw [heq]
    exact hy
  · intro S hS
    obtain ⟨i, hi⟩ :=
      Partite.Induced.Initial.irreducible_same_index B β S hS
    intro x hx y hy hxy
    apply Prod.ext
    · exact (hi ⟨x, hx⟩).trans (hi ⟨y, hy⟩).symm
    · exact hxy
  · intro S hS R x hxS hB
    obtain ⟨i, hi⟩ :=
      Partite.Induced.Initial.irreducible_same_index B β S hS
    let y : Fin (L.arity R) → V := Prod.snd ∘ x
    refine ⟨i, y, hB, ?_⟩
    funext k
    apply Prod.ext
    · exact hi ⟨x k, hxS k⟩
    · rfl

/-- The initial disjoint-union picture is locally tree-like at every finite
scale. -/
theorem initial_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V)
    (β : I → V ↪ P) [Nonempty I]
    (hA : A.Irreducible) (n : ℕ) :
    RelStructure.LocallyTreeLike A B
      (Partite.Initial.picture B β).toRelStructure n := by
  intro S _
  refine ⟨V, B, RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl B), ?_⟩
  let f : ↥(↑S : Set (I × V)) → V := fun x => x.1.2
  have hFold := initial_fold_isHomomorphismEmbedding B β
  have hIncl :
      ((Partite.Initial.picture B β).toRelStructure.induce
        (↑S : Set (I × V))).IsHomomorphismEmbedding
        (Partite.Initial.picture B β).toRelStructure Subtype.val :=
    (RelStructure.inclusion
      (Partite.Initial.picture B β).toRelStructure
      (↑S : Set (I × V))).isHomomorphismEmbedding
  have hf :
      ((Partite.Initial.picture B β).toRelStructure.induce
        (↑S : Set (I × V))).IsHomomorphismEmbedding B f := by
    change ((Partite.Initial.picture B β).toRelStructure.induce
      (↑S : Set (I × V))).IsHomomorphismEmbedding B
        (Prod.snd ∘ Subtype.val)
    exact hFold.comp hIncl
  refine ⟨f, hf, ?_⟩
  intro α
  obtain ⟨α', hα'⟩ := hFold.after_irreducible_embedding hA α
  refine ⟨α', ?_⟩
  intro a ha
  refine ⟨a, ?_⟩
  change Prod.snd (α a) = α' a
  exact (hα' a).symm

end StructuralRamsey.Partite.Iterated

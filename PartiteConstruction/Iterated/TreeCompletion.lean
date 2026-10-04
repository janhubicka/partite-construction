import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Iterated.Initial

/-! # Local completion into tree amalgams

The sparsening theorem itself needs only the following property: every small
induced substructure homomorphism-embeds into a tree amalgam of copies of B.
It does not require the additional ambient-A-copy control built into
`LocallyTreeLike`.

This file isolates that weaker invariant.  It is the natural target for the
classical completion-based iterated partite argument.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W X : Type v}

/-- A structure admits a completion map into a tree amalgam of Base. -/
def HasTreeCompletion
    (Base : RelStructure L V) (C : RelStructure L W) : Prop :=
  ∃ (Y : Type v) (T : RelStructure L Y),
    TreeAmalgam Base Y T ∧
    ∃ f : W → Y, C.IsHomomorphismEmbedding T f

/-- Every induced substructure on at most n vertices has a tree completion. -/
def LocallyTreeCompletable
    (Base : RelStructure L V) (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    HasTreeCompletion Base (C.induce (↑S : Set W))

namespace LocallyTreeCompletable

variable {Base : RelStructure L V}
variable {C : RelStructure L W} {D : RelStructure L X}
variable {m n : ℕ}

/-- The stronger controlled local-tree invariant implies local tree
completability after forgetting the ambient-control clause. -/
theorem of_locallyTreeLike
    {U : Type v} {A : RelStructure L U}
    (h : LocallyTreeLike A Base C n) :
    LocallyTreeCompletable Base C n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, _⟩ := h S hS
  exact ⟨Y, T, hTree, f, hf⟩

/-- Monotonicity in the size bound. -/
theorem mono
    (h : LocallyTreeCompletable Base C n) (hmn : m ≤ n) :
    LocallyTreeCompletable Base C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- Pull local tree completability back along an induced embedding. -/
theorem pullback_embedding
    (hC : LocallyTreeCompletable Base C n)
    (e : Embedding D C) :
    LocallyTreeCompletable Base D n := by
  classical
  intro S hS
  let I : Finset W := S.image e
  have hcard : I.card = S.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Y, T, hTree, fC, hfC⟩ := hC I (by
    rw [hcard]
    exact hS)
  let eS : Embedding (D.induce (↑S : Set X)) (C.induce (↑I : Set W)) := {
    toFun := fun x =>
      ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change C.rel R (e ∘ (Subtype.val ∘ x)) ↔
        D.rel R (Subtype.val ∘ x)
      exact e.map_rel_iff R (Subtype.val ∘ x)
  }
  exact ⟨Y, T, hTree, fC ∘ eS,
    hfC.comp eS.isHomomorphismEmbedding⟩

/-- Pull a tree completion back along a homomorphism-embedding whenever the
image of the tested set fits the available size bound. -/
theorem witness_of_homEmbedding_image
    [DecidableEq X]
    (hD : LocallyTreeCompletable Base D m)
    (p : W → X) (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hcard : (S.image p).card ≤ m) :
    HasTreeCompletion Base (C.induce (↑S : Set W)) := by
  classical
  let I : Finset X := S.image p
  obtain ⟨Y, T, hTree, g, hg⟩ := hD I hcard
  let pS : ↥(↑S : Set W) → ↥(↑I : Set X) :=
    fun x => ⟨p x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hToD :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding D
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hpS :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding
        (D.induce (↑I : Set X)) pS :=
    hToD.codRestrict (↑I : Set X)
      (fun x => Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩)
  exact ⟨Y, T, hTree, g ∘ pS, hg.comp hpS⟩

/-- If C homomorphism-embeds into Base, every finite part of C has the
one-copy tree completion Base. -/
theorem of_homEmbedding_to_base
    (p : W → V) (hp : C.IsHomomorphismEmbedding Base p) (n : ℕ) :
    LocallyTreeCompletable Base C n := by
  intro S _
  let f : ↥(↑S : Set W) → V := p ∘ Subtype.val
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  exact ⟨V, Base, TreeAmalgam.copy (Iso.refl Base),
    f, hp.comp hIncl⟩

/-- The disjoint-union initial picture is locally tree completable at every
scale, without any irreducibility hypothesis on a control structure. -/
theorem initial
    {P I : Type v}
    (Base : RelStructure L V) (β : I → V ↪ P) [Nonempty I]
    (n : ℕ) :
    LocallyTreeCompletable Base
      (Partite.Initial.picture Base β).toRelStructure n :=
  of_homEmbedding_to_base Prod.snd
    (Partite.Iterated.initial_fold_isHomomorphismEmbedding Base β) n

end LocallyTreeCompletable
end StructuralRamsey.RelStructure

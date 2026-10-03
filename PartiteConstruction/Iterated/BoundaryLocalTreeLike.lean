import PartiteConstruction.Iterated.BoundaryControlSystem

/-! # Boundary-compatible local tree-likeness

This is the relative invariant suggested by the mixed-overlap obstruction.
A witness for a tested set carries, for every ambient A-copy, an induced
embedding of its tested boundary into the target tree.  The boundary image is
required to lie inside an irreducible target substructure.

Unlike hereditary irreducibility, this is data carried by the construction.
Given A irreducible and A embedding into B, the boundary system can be
completed to the ordinary ambient-A control clause.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- Local tree witnesses equipped with induced boundary data for all ambient
A-copies. -/
def BoundaryLocallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        Nonempty
          (LocallyTreeLike.BoundarySystem A C T S f)

namespace BoundaryLocallyTreeLike

variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {D : RelStructure L X}
variable {m n : ℕ}

/-- Boundary-compatible local tree-likeness is monotone in the size bound. -/
theorem mono
    (h : BoundaryLocallyTreeLike A B C n) (hmn : m ≤ n) :
    BoundaryLocallyTreeLike A B C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- Forget the boundary data by completing ordinary ambient-A control.
Only irreducibility of A is required. -/
theorem toLocallyTreeLike
    [Finite U] [Finite W]
    (hA : A.Irreducible) (eAB : Embedding A B)
    (h : BoundaryLocallyTreeLike A B C n) :
    LocallyTreeLike A B C n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, hbd⟩ := h S hS
  exact LocallyTreeLike.completeControl_of_boundaries
    (A := A) (B := B) (C := C)
    hA eAB S hTree f hf (Classical.choice hbd)

/-- A structure homomorphism-embedding into irreducible A has the boundary
invariant at every level, provided A embeds into B. -/
theorem of_homEmbedding_to_base
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (p : W → U) (hp : C.IsHomomorphismEmbedding A p)
    (n : ℕ) :
    BoundaryLocallyTreeLike A B C n := by
  classical
  intro S _
  let f : ↥(↑S : Set W) → V := fun x => eAB (p x.1)
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hToA :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding A
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding B f := by
    change (C.induce (↑S : Set W)).IsHomomorphismEmbedding B
      (eAB ∘ (p ∘ Subtype.val))
    exact eAB.isHomomorphismEmbedding.comp hToA
  let hbd :
      LocallyTreeLike.BoundarySystem A C B S f := {
    get := fun α => by
      obtain ⟨q, hq⟩ := hp.after_irreducible_embedding hA α
      let Hset : Set U := {a : U | α a ∈ S}
      let boundary : Embedding (A.induce Hset) B :=
        (eAB.comp q).comp (inclusion A Hset)
      refine {
        boundary := boundary
        agrees := ?_
        contained := ?_
      }
      · intro x
        change eAB (q x.1) = eAB (p (α x.1))
        exact congrArg eAB (hq x.1)
      · apply Embedding.containedInIrreducible_of_range_subset
          hA (eAB.comp q) boundary
        intro x
        exact ⟨x.1, rfl⟩
  }
  exact ⟨V, B, TreeAmalgam.copy (Iso.refl B),
    f, hf, ⟨hbd⟩⟩

/-- Pull the boundary invariant back along an induced embedding. -/
theorem pullback_embedding
    (hC : BoundaryLocallyTreeLike A B C n)
    (e : Embedding D C) :
    BoundaryLocallyTreeLike A B D n := by
  classical
  intro S hS
  let I : Finset W := S.image e
  have hcard : I.card = S.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Y, T, hTree, fC, hfC, hbdC⟩ :=
    hC I (by simpa [hcard] using hS)
  let eS : ↥(↑S : Set X) → ↥(↑I : Set W) :=
    fun x => ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  let ee : Embedding (D.induce (↑S : Set X))
      (C.induce (↑I : Set W)) := {
    toFun := eS
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
  let f : ↥(↑S : Set X) → Y := fC ∘ ee
  have hf :
      (D.induce (↑S : Set X)).IsHomomorphismEmbedding T f :=
    hfC.comp ee.isHomomorphismEmbedding
  let old := Classical.choice hbdC
  let hbd :
      LocallyTreeLike.BoundarySystem A D T S f := {
    get := fun α => by
      let αC : Embedding A C := e.comp α
      let bdC := old.get αC
      let HD : Set U := {a : U | α a ∈ S}
      let HC : Set U := {a : U | αC a ∈ I}
      let j : Embedding (A.induce HD) (A.induce HC) := {
        toFun := fun x => ⟨x.1,
          Finset.mem_image.mpr ⟨α x.1, x.2, rfl⟩⟩
        injective := by
          intro x y hxy
          apply Subtype.ext
          exact congrArg (fun q : HC => q.1) hxy
        map_rel_iff := fun _ _ => Iff.rfl
      }
      refine {
        boundary := bdC.boundary.comp j
        agrees := ?_
        contained := by
          rcases bdC.contained with ⟨R, hR, hsub⟩
          refine ⟨R, hR, ?_⟩
          intro x
          exact hsub (j x)
      }
      intro x
      change bdC.boundary (j x) = fC (ee ⟨α x.1, x.2⟩)
      rw [bdC.agrees (j x)]
      apply congrArg fC
      apply Subtype.ext
      rfl
  }
  exact ⟨Y, T, hTree, f, hf, ⟨hbd⟩⟩

end BoundaryLocallyTreeLike
end StructuralRamsey.RelStructure

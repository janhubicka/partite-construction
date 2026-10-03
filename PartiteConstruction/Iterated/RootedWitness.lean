import PartiteConstruction.Iterated.LocalTreeLike

/-! # Local-tree witnesses with a retained irreducible root

A small test set can meet an irreducible gluing root in a reducible subset.
Rather than claim that a homomorphism-embedding is induced on that subset,
include the entire root in the tested set.  This costs at most the cardinality
of the root, and gives a genuine root embedding into the tree witness.

The root need not be hereditarily irreducible.  The conclusion records the
compatibility needed to glue a fresh base copy over the whole root, even when
the source overlap seen by the small test set is smaller.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB X H E : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Core : RelStructure L X} {Root : RelStructure L H}
variable {Side : RelStructure L E}

/-- Test a finite embedded side together with the whole irreducible root.
The two maps into the resulting tree agree wherever the original embeddings
into the core agree. -/
theorem rootedWitness
    [Finite H] [Finite E]
    (hRoot : Root.Irreducible)
    (eRoot : Embedding Root Core) (eSide : Embedding Side Core)
    (n : ℕ) (hSideCard : Nat.card E ≤ n)
    (hCore : LocallyTreeLike Control Base Core (n + Nat.card H)) :
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam Base Y T ∧
      ∃ p : E → Y,
        Side.IsHomomorphismEmbedding T p ∧
        ∃ tRoot : Embedding Root T,
          ∀ x d, eSide x = eRoot d → p x = tRoot d := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype E := Fintype.ofFinite E
  let R : Finset X :=
    (Finset.univ.image eSide) ∪ (Finset.univ.image eRoot)
  have hRcard : R.card ≤ n + Nat.card H := by
    calc
      R.card ≤ (Finset.univ.image eSide).card +
          (Finset.univ.image eRoot).card := Finset.card_union_le _ _
      _ ≤ Fintype.card E + Fintype.card H := by
        exact Nat.add_le_add
          (by simpa using (Finset.card_image_le
            (s := (Finset.univ : Finset E)) (f := eSide)))
          (by simpa using (Finset.card_image_le
            (s := (Finset.univ : Finset H)) (f := eRoot)))
      _ ≤ n + Nat.card H := by
        simpa only [Nat.card_eq_fintype_card] using
          Nat.add_le_add_right hSideCard (Nat.card H)
  let Rset : Set X := ↑R
  let CoreR := Core.induce Rset
  let iSide : Embedding Side CoreR := {
    toFun := fun x => ⟨eSide x, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)⟩
    injective := by
      intro x y h
      exact eSide.injective (congrArg Subtype.val h)
    map_rel_iff := fun S x => eSide.map_rel_iff S x
  }
  let iRoot : Embedding Root CoreR := {
    toFun := fun d => ⟨eRoot d, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩)⟩
    injective := by
      intro x y h
      exact eRoot.injective (congrArg Subtype.val h)
    map_rel_iff := fun S x => eRoot.map_rel_iff S x
  }
  obtain ⟨Y, T, hTree, g, hg, _⟩ := hCore R hRcard
  obtain ⟨tRoot, htRoot⟩ := hg.after_irreducible_embedding hRoot iRoot
  let p : E → Y := g ∘ iSide
  have hp : Side.IsHomomorphismEmbedding T p :=
    hg.comp iSide.isHomomorphismEmbedding
  refine ⟨Y, T, hTree, p, hp, tRoot, ?_⟩
  intro x d hxd
  change g (iSide x) = tRoot d
  rw [htRoot d]
  apply congrArg g
  apply Subtype.ext
  exact hxd

end StructuralRamsey.RelStructure.LocallyTreeLike

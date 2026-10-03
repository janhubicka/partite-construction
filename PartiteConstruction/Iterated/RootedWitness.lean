import PartiteConstruction.Iterated.LocalTreeLike

/-! # Local-tree witnesses with a retained irreducible root

A small test set can meet an irreducible gluing root in a reducible subset.
Include the entire root in the tested set instead.  This costs at most its
cardinality and gives a genuine root embedding into the tree witness.
The ambient control clause is retained, avoiding a later completion step.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB X H E : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Core : RelStructure L X} {Root : RelStructure L H}
variable {Side : RelStructure L E}

/-- Test a finite embedded side together with the whole irreducible root,
retaining control of intersections with every ambient Control-copy. -/
theorem rootedWitness_controlled
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
          (∀ x d, eSide x = eRoot d → p x = tRoot d) ∧
          ∀ α : Embedding Control Core,
            ∃ α' : Embedding Control T,
              ∀ x a, eSide x = α a → ∃ a', p x = α' a' := by
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
  obtain ⟨Y, T, hTree, g, hg, hctrl⟩ := hCore R hRcard
  obtain ⟨tRoot, htRoot⟩ := hg.after_irreducible_embedding hRoot iRoot
  let p : E → Y := g ∘ iSide
  have hp : Side.IsHomomorphismEmbedding T p :=
    hg.comp iSide.isHomomorphismEmbedding
  refine ⟨Y, T, hTree, p, hp, tRoot, ?_, ?_⟩
  · intro x d hxd
    change g (iSide x) = tRoot d
    rw [htRoot d]
    apply congrArg g
    apply Subtype.ext
    exact hxd
  · intro α
    obtain ⟨α', hα'⟩ := hctrl α
    refine ⟨α', ?_⟩
    intro x a hxa
    have ha : α a ∈ R := by
      rw [← hxa]
      exact (iSide x).2
    obtain ⟨a', ha'⟩ := hα' a ha
    refine ⟨a', ?_⟩
    change g (iSide x) = α' a'
    have heq : iSide x = (⟨α a, ha⟩ : Rset) := Subtype.ext hxa
    rw [heq]
    exact ha'

/-- The unadorned rooted witness, when ambient control is not needed. -/
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
  obtain ⟨Y, T, hT, p, hp, t, ht, _⟩ :=
    rootedWitness_controlled hRoot eRoot eSide n hSideCard hCore
  exact ⟨Y, T, hT, p, hp, t, ht⟩

end StructuralRamsey.RelStructure.LocallyTreeLike

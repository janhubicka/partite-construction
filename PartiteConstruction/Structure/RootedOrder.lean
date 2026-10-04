import PartiteConstruction.Structure.RootedEmbedding
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false

/-! # Reconstructing the order after the fixed-root reduction

A moving vertex is placed according to the number of root vertices declared
below it by the unary cut predicates.  Invalid cut patterns in irrelevant
witness vertices cause no problem: images of an encoded structure have exactly
the valid cut pattern of their source.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R V W : Type v}

/-- Intrinsic rank in a finite linear order. -/
noncomputable def orderRank (α : Type v) [Fintype α] [LinearOrder α]
    (x : α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun y => y < x)).card

theorem orderRank_strictMono (α : Type v) [Fintype α] [LinearOrder α] :
    StrictMono (orderRank α) := by
  intro a b hab
  unfold orderRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨a, ?_, ?_⟩
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    rcases hx with rfl | hxa
    · exact hab
    · exact lt_trans hxa hab

theorem orderRank_injective (α : Type v) [Fintype α] [LinearOrder α] :
    Function.Injective (orderRank α) :=
  (orderRank_strictMono α).injective

theorem orderRank_lt_iff (α : Type v) [Fintype α] [LinearOrder α]
    (x y : α) :
    orderRank α x < orderRank α y ↔ x < y :=
  (orderRank_strictMono α).lt_iff_lt

/-- Number of fixed-root vertices whose cut predicate holds at x. -/
noncomputable def cutRank
    (C : Structure (language L R) V) [Fintype R] (x : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r => C.rel (.cut r) ![x])).card

/-- A reduced embedding preserves the cut rank exactly. -/
theorem cutRank_embedding
    {C : Structure (language L R) V}
    {D : Structure (language L R) W}
    [Fintype R] (e : Structure.Embedding C D) (x : V) :
    cutRank D (e x) = cutRank C x := by
  classical
  unfold cutRank
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hm := e.map_rel_iff (.cut r) ![x]
  have ht : e ∘ ![x] = ![e x] := by
    funext i
    fin_cases i
    rfl
  rw [ht] at hm
  exact hm

/-- Root vertices lying below an outside vertex in an encoded ordered
structure. -/
noncomputable def rootBelow
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (x : Outside ρ) : Finset R := by
  classical
  exact Finset.univ.filter (fun r => ρ r < x.1)

theorem cutRank_encode
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (x : Outside ρ) :
    cutRank (encode ρ) x = (rootBelow ρ x).card := by
  classical
  unfold cutRank rootBelow
  apply congrArg Finset.card
  ext r
  simp [encode]

/-- For an order-preserving root embedding, its intrinsic rank is the number
of root points below its image. -/
theorem rootBelowRoot_card
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ) (r : R) :
    (Finset.univ.filter (fun s => ρ s < ρ r)).card = orderRank R r := by
  classical
  unfold orderRank
  apply congrArg Finset.card
  ext s
  simp [hρ.lt_iff_lt]

/-- If r lies below x, the rank of r is strictly smaller than the number of
root points below x. -/
theorem orderRank_lt_rootBelow_card
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ)
    (r : R) (x : Outside ρ) (hrx : ρ r < x.1) :
    orderRank R r < (rootBelow ρ x).card := by
  classical
  unfold orderRank rootBelow
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨r, ?_, ?_⟩
  · simp
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs ⊢
    rcases hs with rfl | hsr
    · exact hrx
    · exact lt_trans (hρ hsr) hrx

/-- If r is not below x, the number of root points below x is at most the
rank of r. -/
theorem rootBelow_card_le_orderRank
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ)
    (r : R) (x : Outside ρ) (hrx : ¬ ρ r < x.1) :
    (rootBelow ρ x).card ≤ orderRank R r := by
  classical
  unfold orderRank rootBelow
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  by_contra hsr
  have hrs : r ≤ s := le_of_not_gt hsr
  exact hrx (lt_of_le_of_lt (hρ.monotone hrs) hs)

/-- Root-below sets are monotone along the ambient order. -/
theorem rootBelow_card_mono
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder V]
    (ρ : Structure.Embedding Root A)
    (x y : Outside ρ) (hxy : x.1 < y.1) :
    (rootBelow ρ x).card ≤ (rootBelow ρ y).card := by
  classical
  unfold rootBelow
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact lt_trans hr hxy

/-- Lexicographic code for the reconstructed ordered carrier.  A moving
vertex of cut rank k is placed immediately before the k-th root vertex; moving
vertices in the same cut retain the witness order. -/
noncomputable def orderKey
    (Root : Structure L R) (C : Structure (language L R) V)
    [Fintype R] [LinearOrder R] [Fintype V] [LinearOrder V] :
    Sum R V → Nat ×ₗ (Bool ×ₗ Nat)
  | .inl r => toLex (orderRank R r, toLex (true, orderRank R r))
  | .inr x => toLex (cutRank C x, toLex (false, orderRank V x))

theorem orderKey_injective
    (Root : Structure L R) (C : Structure (language L R) V)
    [Fintype R] [LinearOrder R] [Fintype V] [LinearOrder V] :
    Function.Injective (orderKey Root C) := by
  intro x y h
  cases x with
  | inl r =>
      cases y with
      | inl s =>
          apply congrArg Sum.inl
          apply orderRank_injective R
          exact congrArg (fun z => (ofLex z).1) h
      | inr y =>
          have hb := congrArg (fun z => (ofLex (ofLex z).2).1) h
          simp [orderKey] at hb
  | inr x =>
      cases y with
      | inl s =>
          have hb := congrArg (fun z => (ofLex (ofLex z).2).1) h
          simp [orderKey] at hb
      | inr y =>
          apply congrArg Sum.inr
          apply orderRank_injective V
          exact congrArg (fun z => (ofLex (ofLex z).2).2) h

/-- Canonical reconstructed order on root plus moving vertices. -/
noncomputable def reconstructedOrder
    (Root : Structure L R) (C : Structure (language L R) V)
    [Fintype R] [LinearOrder R] [Fintype V] [LinearOrder V] :
    LinearOrder (Sum R V) :=
  LinearOrder.lift' (orderKey Root C) (orderKey_injective Root C)

theorem reconstructed_lt_iff_key
    (Root : Structure L R) (C : Structure (language L R) V)
    [Fintype R] [LinearOrder R] [Fintype V] [LinearOrder V]
    (x y : Sum R V) :
    @LT.lt (Sum R V) (reconstructedOrder Root C).toLT x y ↔
      orderKey Root C x < orderKey Root C y :=
  Iff.rfl

/-- A reduced full ordered embedding lifts to a full ordered embedding after
reattaching the root, provided the source root embedding preserves order. -/
noncomputable def liftOrderedEmbedding
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [Fintype V] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ)
    {C : Structure (language L R) W}
    [Fintype W] [LinearOrder W]
    (e : Structure.Embedding
      (encode ρ).withLinearOrder C.withLinearOrder) :
    Structure.Embedding A.withLinearOrder
      (@Structure.withLinearOrder L (Sum R W) (decode Root C)
        (reconstructedOrder Root C).toLT) := by
  let e0 : Structure.Embedding (encode ρ) C := e.linearOrderReduct
  let g : Structure.Embedding A (decode Root C) :=
    (decodeEmbedding Root e0).comp (splitEmbedding ρ)
  have hemono : StrictMono e0 := e.strictMono
  have hg_apply (z : V) :
      g z = sumMap e0 (split ρ z) := rfl
  have hgmono : StrictMono g := by
    intro a b hab
    cases hsa : split ρ a with
    | inl r =>
        cases hsb : split ρ b with
        | inl s =>
            have hua := unsplit_split ρ a
            have hub := unsplit_split ρ b
            rw [hsa] at hua
            rw [hsb] at hub
            have hrs : r < s := by
              apply (hρ.lt_iff_lt).mp
              simpa [hua, hub] using hab
            rw [hg_apply a, hg_apply b, hsa, hsb]
            apply (reconstructed_lt_iff_key Root C _ _).2
            exact Prod.Lex.toLex_lt_toLex.mpr
              (Or.inl ((orderRank_lt_iff R r s).2 hrs))
        | inr y =>
            have hua := unsplit_split ρ a
            have hub := unsplit_split ρ b
            rw [hsa] at hua
            rw [hsb] at hub
            have hrx : ρ r < y.1 := by
              simpa [hua, hub] using hab
            have hk :
                orderRank R r < cutRank C (e0 y) := by
              rw [cutRank_embedding e0, cutRank_encode]
              exact orderRank_lt_rootBelow_card ρ hρ r y hrx
            rw [hg_apply a, hg_apply b, hsa, hsb]
            apply (reconstructed_lt_iff_key Root C _ _).2
            exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hk)
    | inr x =>
        cases hsb : split ρ b with
        | inl r =>
            have hua := unsplit_split ρ a
            have hub := unsplit_split ρ b
            rw [hsa] at hua
            rw [hsb] at hub
            have hxr : x.1 < ρ r := by
              simpa [hua, hub] using hab
            have hnot : ¬ ρ r < x.1 :=
              not_lt_of_ge (le_of_lt hxr)
            have hk :
                cutRank C (e0 x) ≤ orderRank R r := by
              rw [cutRank_embedding e0, cutRank_encode]
              exact rootBelow_card_le_orderRank ρ hρ r x hnot
            rw [hg_apply a, hg_apply b, hsa, hsb]
            apply (reconstructed_lt_iff_key Root C _ _).2
            by_cases hstrict : cutRank C (e0 x) < orderRank R r
            · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrict)
            · have heq : cutRank C (e0 x) = orderRank R r :=
                le_antisymm hk (le_of_not_gt hstrict)
              apply Prod.Lex.toLex_lt_toLex.mpr
              refine Or.inr ⟨heq, ?_⟩
              apply Prod.Lex.toLex_lt_toLex.mpr
              exact Or.inl (by simp)
        | inr y =>
            have hua := unsplit_split ρ a
            have hub := unsplit_split ρ b
            rw [hsa] at hua
            rw [hsb] at hub
            have hxy : x.1 < y.1 := by
              simpa [hua, hub] using hab
            have hk :
                cutRank C (e0 x) ≤ cutRank C (e0 y) := by
              rw [cutRank_embedding e0, cutRank_embedding e0,
                cutRank_encode, cutRank_encode]
              exact rootBelow_card_mono ρ x y hxy
            rw [hg_apply a, hg_apply b, hsa, hsb]
            apply (reconstructed_lt_iff_key Root C _ _).2
            by_cases hstrict : cutRank C (e0 x) < cutRank C (e0 y)
            · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrict)
            · have heq : cutRank C (e0 x) = cutRank C (e0 y) :=
                le_antisymm hk (le_of_not_gt hstrict)
              apply Prod.Lex.toLex_lt_toLex.mpr
              refine Or.inr ⟨heq, ?_⟩
              apply Prod.Lex.toLex_lt_toLex.mpr
              refine Or.inr ⟨rfl, ?_⟩
              apply (orderRank_lt_iff W _ _).2
              exact hemono hxy
  exact {
    toFun := g
    injective := g.injective
    map_func := g.map_func
    map_rel_iff := fun S x => by
      cases S with
      | inl S => exact g.map_rel_iff S x
      | inr r =>
          cases r
          change g (x (0 : Fin 2)) < g (x (1 : Fin 2)) ↔
            x (0 : Fin 2) < x (1 : Fin 2)
          exact hgmono.lt_iff_lt
  }

end StructuralRamsey.Rooted

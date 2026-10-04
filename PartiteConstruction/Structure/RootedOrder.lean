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
    (x : α) : ℕ :=
  @Fintype.card (Set.Iio x) (Fintype.ofFinite (Set.Iio x))

theorem orderRank_strictMono (α : Type v) [Fintype α] [LinearOrder α] :
    StrictMono (orderRank α) := by
  intro a b hab
  letI : Fintype (Set.Iio a) := Fintype.ofFinite _
  letI : Fintype (Set.Iio b) := Fintype.ofFinite _
  apply Set.card_lt_card
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    exact lt_trans hx hab
  · intro hEq
    have ha : a ∈ Set.Iio b := hab
    have haa : a ∈ Set.Iio a := by
      rw [hEq]
      exact ha
    exact (lt_irrefl a haa)

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
  letI : Fintype (Set.Iio r) := Fintype.ofFinite _
  have hset :
      (Finset.univ.filter (fun s => ρ s < ρ r) : Finset R) =
        Finset.univ.filter (fun s => s < r) := by
    ext s
    simp [hρ.lt_iff_lt]
  rw [hset]
  rfl

/-- If r lies below x, the rank of r is strictly smaller than the number of
root points below x. -/
theorem orderRank_lt_rootBelow_card
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ)
    (r : R) (x : Outside ρ) (hrx : ρ r < x.1) :
    orderRank R r < (rootBelow ρ x).card := by
  classical
  let S : Set R := {s | s < r}
  let T : Set R := {s | ρ s < x.1}
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  have hST : S ⊂ T := by
    constructor
    · intro s hs
      exact lt_trans (hρ hs) hrx
    · intro heq
      have hrT : r ∈ T := hrx
      have hrS : r ∈ S := by rw [heq]; exact hrT
      exact (lt_irrefl r hrS)
  have hc := Set.card_lt_card hST
  simpa [orderRank, rootBelow, S, T] using hc

/-- If r is not below x, the number of root points below x is at most the
rank of r. -/
theorem rootBelow_card_le_orderRank
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder R] [LinearOrder V]
    (ρ : Structure.Embedding Root A) (hρ : StrictMono ρ)
    (r : R) (x : Outside ρ) (hrx : ¬ ρ r < x.1) :
    (rootBelow ρ x).card ≤ orderRank R r := by
  classical
  let S : Set R := {s | ρ s < x.1}
  let T : Set R := {s | s < r}
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  have hST : S ⊆ T := by
    intro s hs
    by_contra hsr
    have hrs : r ≤ s := le_of_not_gt hsr
    have hρrs : ρ r ≤ ρ s := hρ.monotone hrs
    exact hrx (lt_of_le_of_lt hρrs hs)
  have hc := Set.card_le_card hST
  simpa [orderRank, rootBelow, S, T] using hc

/-- Root-below sets are monotone along the ambient order. -/
theorem rootBelow_card_mono
    {Root : Structure L R} {A : Structure L V}
    [Fintype R] [LinearOrder V]
    (ρ : Structure.Embedding Root A)
    (x y : Outside ρ) (hxy : x.1 < y.1) :
    (rootBelow ρ x).card ≤ (rootBelow ρ y).card := by
  classical
  apply Finset.card_le_card
  intro r hr
  simp [rootBelow] at hr ⊢
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
  let e0 := e.linearOrderReduct
  let g : Structure.Embedding A (decode Root C) :=
    (decodeEmbedding Root e0).comp (splitEmbedding ρ)
  have hemono : StrictMono e0 := e.strictMono
  have hgmono : StrictMono g := by
    intro a b hab
    let sa := split ρ a
    let sb := split ρ b
    have hua : unsplit ρ sa = a := unsplit_split ρ a
    have hub : unsplit ρ sb = b := unsplit_split ρ b
    cases hsa : sa with
    | inl r =>
        cases hsb : sb with
        | inl s =>
            have har : a = ρ r := by
              rw [← hua, hsa]
              rfl
            have hbs : b = ρ s := by
              rw [← hub, hsb]
              rfl
            have hrs : r < s := by
              apply (hρ.lt_iff_lt).mp
              simpa [har, hbs] using hab
            change
              @LT.lt (Sum R W) (reconstructedOrder Root C).toLT
                (Sum.inl r) (Sum.inl s)
            change orderKey Root C (Sum.inl r) <
              orderKey Root C (Sum.inl s)
            exact Prod.Lex.toLex_lt_toLex.mpr
              (Or.inl ((orderRank_lt_iff R r s).2 hrs))
        | inr y =>
            have har : a = ρ r := by
              rw [← hua, hsa]
              rfl
            let x : Outside ρ := by
              have : Sum.inr x = sb := hsb.symm
              exact x
            have hbx : b = x.1 := by
              rw [← hub, hsb]
              rfl
            have hrx : ρ r < x.1 := by simpa [har, hbx] using hab
            have hk :
                orderRank R r < cutRank C (e0 x) := by
              rw [cutRank_embedding e0, cutRank_encode]
              exact orderRank_lt_rootBelow_card ρ hρ r x hrx
            change orderKey Root C (Sum.inl r) <
              orderKey Root C (Sum.inr (e0 x))
            exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hk)
    | inr x =>
        cases hsb : sb with
        | inl r =>
            have hax : a = x.1 := by
              rw [← hua, hsa]
              rfl
            have hbr : b = ρ r := by
              rw [← hub, hsb]
              rfl
            have hnot : ¬ ρ r < x.1 := by
              exact not_lt_of_ge (le_of_lt (by simpa [hax, hbr] using hab))
            have hk :
                cutRank C (e0 x) ≤ orderRank R r := by
              rw [cutRank_embedding e0, cutRank_encode]
              exact rootBelow_card_le_orderRank ρ hρ r x hnot
            change orderKey Root C (Sum.inr (e0 x)) <
              orderKey Root C (Sum.inl r)
            by_cases hstrict : cutRank C (e0 x) < orderRank R r
            · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrict)
            · have heq : cutRank C (e0 x) = orderRank R r :=
                le_antisymm hk (le_of_not_gt hstrict)
              apply Prod.Lex.toLex_lt_toLex.mpr
              exact Or.inr ⟨heq, by
                apply Prod.Lex.toLex_lt_toLex.mpr
                exact Or.inl (by simp)⟩
        | inr y =>
            have hax : a = x.1 := by
              rw [← hua, hsa]
              rfl
            have hby : b = y.1 := by
              rw [← hub, hsb]
              rfl
            have hxy : x.1 < y.1 := by simpa [hax, hby] using hab
            have hk :
                cutRank C (e0 x) ≤ cutRank C (e0 y) := by
              rw [cutRank_embedding e0, cutRank_embedding e0,
                cutRank_encode, cutRank_encode]
              exact rootBelow_card_mono ρ x y hxy
            change orderKey Root C (Sum.inr (e0 x)) <
              orderKey Root C (Sum.inr (e0 y))
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
      | inr _ => exact hgmono.lt_iff_lt
  }

end StructuralRamsey.Rooted

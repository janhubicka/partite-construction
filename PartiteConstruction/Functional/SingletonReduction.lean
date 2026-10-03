import PartiteConstruction.Functional.SingletonExpansion

/-! # Ramsey reduction to singleton-valued functions

For a finite ordered pair A,B, take
  N = max(|A|, |B|)
and replace every set-valued function F by its N ordered rank functions.
Every new function has empty-or-singleton values.

This file proves the converse coding step needed for the WLOG reduction:
a structure in the ranked language can be reduced by taking the union of all
rank fibres, ranked embeddings can be forgotten, and a Ramsey arrow for the
ranked singleton expansions descends to a Ramsey arrow for the original pair.

The only order-specific input is that embeddings A -> B are strictly
monotone.  In the survey this follows from the distinguished linear order.
-/
namespace StructuralRamsey.Structure

open StructuralRamsey

universe u v w z

variable {L : Language.{u}}
variable {V : Type v} {W : Type w} {X : Type z}

/-- Forget the rank labels by taking the union of all ranked function fibres. -/
def rankReduct
    {n : ℕ} (C : Structure (L.rankFunctions n) X) :
    Structure L X where
  rel R x := C.rel R x
  func F x := {y | ∃ i : Fin n, y ∈ C.func (F, i) x}

/-- All fibres of A are represented by the first n rank functions. -/
def RankCovered
    (A : Structure L V) [Finite V] (n : ℕ) : Prop :=
  ∀ F x, (fiberFinset A F x).card ≤ n

/-- Using as many ranks as vertices certainly covers every fibre. -/
theorem rankCovered_card
    (A : Structure L V) [Fintype V] :
    RankCovered A (Fintype.card V) := by
  intro F x
  exact fiberFinset_card_le A F x

/-- Fibre coverage is monotone in the number of available ranks. -/
theorem RankCovered.mono
    {A : Structure L V} [Finite V] {m n : ℕ}
    (h : RankCovered A m) (hmn : m ≤ n) :
    RankCovered A n := by
  intro F x
  exact (h F x).trans hmn

/-- The common rank bound max(|A|,|B|) covers A. -/
theorem rankCovered_pair_left
    (A : Structure L V) (B : Structure L W)
    [Fintype V] [Fintype W] :
    RankCovered A (max (Fintype.card V) (Fintype.card W)) :=
  (rankCovered_card A).mono (Nat.le_max_left _ _)

/-- The common rank bound max(|A|,|B|) covers B. -/
theorem rankCovered_pair_right
    (A : Structure L V) (B : Structure L W)
    [Fintype V] [Fintype W] :
    RankCovered B (max (Fintype.card V) (Fintype.card W)) :=
  (rankCovered_card B).mono (Nat.le_max_right _ _)

/-- A ranked embedding forgets to an embedding for the original set-valued
functions, provided all source fibres are covered by the available ranks. -/
noncomputable def Embedding.forgetRanks
    {A : Structure L V}
    {n : ℕ}
    [LinearOrder V] [Finite V]
    {C : Structure (L.rankFunctions n) X}
    (e : Embedding (rankExpand A n) C)
    (hA : RankCovered A n) :
    Embedding A (rankReduct C) where
  toFun := e
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, hai⟩ :=
        mem_rankedValue_of_mem A n F x (hA F x) ha
      refine ⟨i, ?_⟩
      have hm :
          e a ∈ imageSet e ((rankExpand A n).func (F, i) x) :=
        ⟨a, hai, rfl⟩
      rw [e.map_func (F, i) x] at hm
      exact hm
    · rintro ⟨i, hy⟩
      have hm :
          y ∈ imageSet e ((rankExpand A n).func (F, i) x) := by
        rw [e.map_func (F, i) x]
        exact hy
      rcases hm with ⟨a, ha, hea⟩
      refine ⟨a, ?_, hea⟩
      change a ∈ rankedValue A n F i x at ha
      exact rankedValue_subset A n F i x ha

@[simp] theorem Embedding.forgetRanks_apply
    {A : Structure L V}
    {n : ℕ}
    [LinearOrder V] [Finite V]
    {C : Structure (L.rankFunctions n) X}
    (e : Embedding (rankExpand A n) C)
    (hA : RankCovered A n) (x : V) :
    e.forgetRanks hA x = e x := rfl

/-- Forgetting ranks commutes with composing a ranked lift of an
order-preserving embedding. -/
theorem Embedding.forgetRanks_comp_rankExpand
    {A : Structure L V} {B : Structure L W}
    {n : ℕ}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    {C : Structure (L.rankFunctions n) X}
    (e : Embedding A B) (hmono : StrictMono e)
    (g : Embedding (rankExpand B n) C)
    (hA : RankCovered A n) (hB : RankCovered B n) :
    (g.comp (e.rankExpand hmono n)).forgetRanks hA =
      (g.forgetRanks hB).comp e := by
  apply Embedding.ext
  intro x
  rfl

/-- Ramsey arrows descend from the canonical ranked singleton expansions. -/
theorem arrow_of_rankExpansion
    (A : Structure L V) (B : Structure L W)
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (n : ℕ)
    (hA : RankCovered A n) (hB : RankCovered B n)
    (hmono : ∀ e : Embedding A B, StrictMono e)
    (C : Structure (L.rankFunctions n) X)
    (κ : Type*)
    (hRamsey : Arrow (rankExpand A n) (rankExpand B n) C κ) :
    Arrow A B (rankReduct C) κ := by
  intro χ
  let χ' : Embedding (rankExpand A n) C → κ :=
    fun e => χ (e.forgetRanks hA)
  obtain ⟨f, hf⟩ := hRamsey χ'
  let f0 : Embedding B (rankReduct C) := f.forgetRanks hB
  refine ⟨f0, ?_⟩
  intro e₁ e₂
  have hh :=
    hf (e₁.rankExpand (hmono e₁) n)
      (e₂.rankExpand (hmono e₂) n)
  change
    χ ((f.comp (e₁.rankExpand (hmono e₁) n)).forgetRanks hA) =
      χ ((f.comp (e₂.rankExpand (hmono e₂) n)).forgetRanks hA) at hh
  rw [Embedding.forgetRanks_comp_rankExpand
        e₁ (hmono e₁) f hA hB,
      Embedding.forgetRanks_comp_rankExpand
        e₂ (hmono e₂) f hA hB] at hh
  exact hh

/-- Pairwise WLOG reduction used in the ordered Ramsey theorem.  Splitting
fibres into N=max(|A|,|B|) ordered ranks makes every function singleton-valued,
and any Ramsey witness for the expanded pair reduces to one for A,B. -/
theorem arrow_of_singletonExpansion
    (A : Structure L V) (B : Structure L W)
    [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
    (hmono : ∀ e : Embedding A B, StrictMono e)
    (C : Structure
      (L.rankFunctions (max (Fintype.card V) (Fintype.card W))) X)
    (κ : Type*)
    (hRamsey :
      Arrow
        (rankExpand A (max (Fintype.card V) (Fintype.card W)))
        (rankExpand B (max (Fintype.card V) (Fintype.card W)))
        C κ) :
    Arrow A B (rankReduct C) κ := by
  exact arrow_of_rankExpansion A B
    (max (Fintype.card V) (Fintype.card W))
    (rankCovered_pair_left A B)
    (rankCovered_pair_right A B)
    hmono C κ hRamsey

end StructuralRamsey.Structure

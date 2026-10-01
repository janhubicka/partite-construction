import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Monotone.Basic

/-! # Finite Ramsey theorem for increasing tuples

A small reusable finite Ramsey core tailored to the partite construction.
The proof is the classical Erdős--Rado induction: build a long chain whose
higher-arity colour is determined by its first element, then apply the
pigeonhole principle. This implementation follows the same proof architecture
as the tuple-Ramsey formalization in the Lax archive, but only keeps the
strictly increasing fragment needed here.
-/
namespace StructuralRamsey.FiniteRamsey

private def chainBound : (ℕ → ℕ) → ℕ → ℕ
  | _, 0 => 0
  | ih, T + 1 => ih (chainBound ih T) + 1

private lemma buildChain (k m : ℕ) (bound : ℕ → ℕ)
    (hbound : ∀ (r : ℕ) {n : ℕ} (S : Finset (Fin n)),
      bound r ≤ S.card → ∀ c : (Fin m → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ r ≤ I.card ∧ ∃ col : Fin k,
          ∀ a : Fin m → Fin n, StrictMono a → (∀ i, a i ∈ I) → c a = col) :
    ∀ (T : ℕ) {n : ℕ} (S : Finset (Fin n))
      (c : (Fin (m + 1) → Fin n) → Fin k),
      chainBound bound T ≤ S.card →
      ∃ I : Finset (Fin n), I ⊆ S ∧ T ≤ I.card ∧
        ∃ cols : Fin n → Fin k,
          ∀ a : Fin (m + 1) → Fin n, StrictMono a → (∀ i, a i ∈ I) →
            c a = cols (a 0) := by
  classical
  intro T
  induction T with
  | zero =>
      intro n S c _
      refine ⟨∅, Finset.empty_subset _, by simp, fun x => c (fun _ => x), ?_⟩
      intro a _ hmem
      exact absurd (hmem 0) (Finset.notMem_empty _)
  | succ T ihT =>
      intro n S c hS
      have hSpos : 0 < S.card := by
        change bound (chainBound bound T) + 1 ≤ S.card at hS
        omega
      have hSne : S.Nonempty := Finset.card_pos.mp hSpos
      let v : Fin n := S.min' hSne
      have hvmem : v ∈ S := S.min'_mem hSne
      let S₁ : Finset (Fin n) := S.erase v
      have hS₁card : bound (chainBound bound T) ≤ S₁.card := by
        have hcard : S₁.card = S.card - 1 := Finset.card_erase_of_mem hvmem
        change bound (chainBound bound T) + 1 ≤ S.card at hS
        omega
      let c' : (Fin m → Fin n) → Fin k := fun b => c (Fin.cons v b)
      obtain ⟨J, hJsub, hJcard, colv, hJhomo⟩ :=
        hbound (chainBound bound T) S₁ hS₁card c'
      obtain ⟨I, hIsub, hIcard, cols, hIhomo⟩ := ihT J c hJcard
      have hvNotI : v ∉ I := by
        intro hv
        have hvJ : v ∈ J := hIsub hv
        have hvS₁ : v ∈ S₁ := hJsub hvJ
        exact (Finset.notMem_erase v S) hvS₁
      have hvLT : ∀ x ∈ S, x ≠ v → v < x := by
        intro x hxS hxne
        have hle : v ≤ x := S.min'_le x hxS
        exact lt_of_le_of_ne hle (Ne.symm hxne)
      refine ⟨insert v I, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxI
        · exact hvmem
        · have hxS₁ : x ∈ S₁ := hJsub (hIsub hxI)
          exact (Finset.mem_erase.mp hxS₁).2
      · rw [Finset.card_insert_of_notMem hvNotI]
        omega
      · refine ⟨fun x => if x = v then colv else cols x, ?_⟩
        intro a ha hmem
        by_cases h0 : a 0 = v
        · have htailMem : ∀ i : Fin m, (Fin.tail a) i ∈ I := by
            intro i
            have hs : a i.succ ∈ insert v I := hmem i.succ
            have hne : a i.succ ≠ v := by
              have hlt : a 0 < a i.succ := ha (Fin.succ_pos i)
              rw [h0] at hlt
              exact ne_of_gt hlt
            rcases Finset.mem_insert.mp hs with heq | hi
            · exact absurd heq hne
            · exact hi
          have htailStrict : StrictMono (Fin.tail a) := by
            intro i j hij
            exact ha (Fin.succ_lt_succ_iff.mpr hij)
          have htailJ : ∀ i, (Fin.tail a) i ∈ J := fun i => hIsub (htailMem i)
          have hc' : c (Fin.cons v (Fin.tail a)) = colv :=
            hJhomo (Fin.tail a) htailStrict htailJ
          have heq : a = Fin.cons v (Fin.tail a) := by
            funext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.cons_zero, h0]
            · intro j
              simp [Fin.cons_succ, Fin.tail]
          have hc : c a = colv := by rw [heq]; exact hc'
          simp [h0, hc]
        · have hallI : ∀ i, a i ∈ I := by
            intro i
            have hi : a i ∈ insert v I := hmem i
            by_cases hiz : i = 0
            · subst hiz
              rcases Finset.mem_insert.mp hi with heq | hI
              · exact absurd heq h0
              · exact hI
            · have ha0S : a 0 ∈ S := by
                rcases Finset.mem_insert.mp (hmem 0) with heq | hI
                · rw [heq]
                  exact hvmem
                · exact (Finset.mem_erase.mp (hJsub (hIsub hI))).2
              have hv0 : v < a 0 := hvLT (a 0) ha0S h0
              have h0i : a 0 < a i := ha (Fin.pos_of_ne_zero hiz)
              have hne : a i ≠ v := ne_of_gt (lt_trans hv0 h0i)
              rcases Finset.mem_insert.mp hi with heq | hI
              · exact absurd heq hne
              · exact hI
          have hc : c a = cols (a 0) := hIhomo a ha hallI
          simp [h0, hc]

private lemma strictMonoRamseyFinset (k : ℕ) :
    ∀ (m M : ℕ), ∃ N : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      N ≤ S.card → ∀ c : (Fin m → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧ ∃ col : Fin k,
          ∀ a : Fin m → Fin n, StrictMono a → (∀ i, a i ∈ I) → c a = col := by
  intro m
  induction m with
  | zero =>
      intro M
      refine ⟨M, ?_⟩
      intro n S hS c
      refine ⟨S, Finset.Subset.rfl, hS, c Fin.elim0, ?_⟩
      intro a _ _
      have ha : a = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [ha]
  | succ m ih =>
      classical
      intro M
      let bound : ℕ → ℕ := fun r => (ih r).choose
      have hbound : ∀ (r : ℕ) {n : ℕ} (S : Finset (Fin n)),
          bound r ≤ S.card → ∀ c : (Fin m → Fin n) → Fin k,
            ∃ I : Finset (Fin n), I ⊆ S ∧ r ≤ I.card ∧ ∃ col : Fin k,
              ∀ a : Fin m → Fin n, StrictMono a →
                (∀ i, a i ∈ I) → c a = col :=
        fun r => (ih r).choose_spec
      let T : ℕ := M * k + 1
      refine ⟨chainBound bound T, ?_⟩
      intro n S hS c
      obtain ⟨I, hIsub, hIcard, cols, hIhomo⟩ :=
        buildChain k m bound hbound T S c hS
      have hcard : k * M < I.card := by
        have h : M * k + 1 ≤ I.card := hIcard
        rw [Nat.mul_comm M k] at h
        omega
      have hex : ∃ col : Fin k, M < (I.filter (fun x => cols x = col)).card := by
        by_contra hneg
        push Not at hneg
        have hsum : ∑ col : Fin k, (I.filter (fun x => cols x = col)).card = I.card := by
          have h := @Finset.card_eq_sum_card_fiberwise _ _ _ cols I
            Finset.univ (fun x _ => Finset.mem_univ _)
          simpa using h.symm
        have hle : ∑ col : Fin k, (I.filter (fun x => cols x = col)).card ≤ k * M := by
          calc
            ∑ col : Fin k, (I.filter (fun x => cols x = col)).card
                ≤ ∑ _col : Fin k, M := Finset.sum_le_sum (fun col _ => hneg col)
            _ = k * M := by simp [Finset.sum_const, Finset.card_univ]
        omega
      obtain ⟨col, hcol⟩ := hex
      refine ⟨I.filter (fun x => cols x = col), ?_, hcol.le, col, ?_⟩
      · exact (Finset.filter_subset _ _).trans hIsub
      · intro a ha hmem
        have hmemI : ∀ i, a i ∈ I := fun i => (Finset.mem_filter.mp (hmem i)).1
        have ha0 : cols (a 0) = col := (Finset.mem_filter.mp (hmem 0)).2
        rw [hIhomo a ha hmemI, ha0]

/-- Finite Ramsey theorem in the exact form needed for increasing placements.
Every colouring of `m`-tuples has a finite ordered set containing `M` points
on which all strictly increasing `m`-tuples have the same colour. -/
theorem strictMono (κ : Type*) [Fintype κ] (m M : ℕ) :
    ∃ N : ℕ, ∀ c : (Fin m → Fin N) → κ,
      ∃ I : Finset (Fin N), M ≤ I.card ∧
        ∀ a b : Fin m → Fin N, StrictMono a → StrictMono b →
          (∀ i, a i ∈ I) → (∀ i, b i ∈ I) → c a = c b := by
  classical
  let e := Fintype.equivFin κ
  obtain ⟨N, hN⟩ := strictMonoRamseyFinset (Fintype.card κ) m M
  refine ⟨N, ?_⟩
  intro c
  obtain ⟨I, -, hIcard, col, hI⟩ := hN Finset.univ (by simp) (fun a => e (c a))
  refine ⟨I, hIcard, ?_⟩
  intro a b ha hb hma hmb
  apply e.injective
  exact (hI a ha hma).trans (hI b hb hmb).symm

end StructuralRamsey.FiniteRamsey

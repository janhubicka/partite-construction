import PartiteConstruction.Ramsey.ClosureUSize2019

/-! # Finite propositional core of the five-vertex seed obstruction

Certified exhaustive calculation on FINSETS of Fin 5. The five closure
dependencies are represented directly, rather than through the
higher-level ClosureRule and IsUIrreducible predicates. Hence these
declarations are finite combinatorial certificates, NOT yet full Lean
formalization of the published semantic definitions.
-/

namespace StructuralRamsey.RelStructure.FiniteSeedObstruction

private abbrev Vert := Fin 5
private abbrev all : Finset Vert := Finset.univ

private def Closed (S : Finset Vert) : Prop :=
  ((0 : Vert) ∈ S → (1 : Vert) ∈ S → (2 : Vert) ∈ S) ∧
  ((0 : Vert) ∈ S → (2 : Vert) ∈ S → (1 : Vert) ∈ S) ∧
  ((1 : Vert) ∈ S → (3 : Vert) ∈ S → (0 : Vert) ∈ S) ∧
  ((2 : Vert) ∈ S → (4 : Vert) ∈ S → (0 : Vert) ∈ S) ∧
  ((3 : Vert) ∈ S → (4 : Vert) ∈ S → (0 : Vert) ∈ S)

private def TupleCover (S T : Finset Vert) : Prop :=
  (((0 : Vert) ∈ S ∧ (1 : Vert) ∈ S ∧ (2 : Vert) ∈ S) ∨
   ((0 : Vert) ∈ T ∧ (1 : Vert) ∈ T ∧ (2 : Vert) ∈ T)) ∧
  (((0 : Vert) ∈ S ∧ (1 : Vert) ∈ S ∧ (3 : Vert) ∈ S) ∨
   ((0 : Vert) ∈ T ∧ (1 : Vert) ∈ T ∧ (3 : Vert) ∈ T)) ∧
  (((0 : Vert) ∈ S ∧ (2 : Vert) ∈ S ∧ (4 : Vert) ∈ S) ∨
   ((0 : Vert) ∈ T ∧ (2 : Vert) ∈ T ∧ (4 : Vert) ∈ T)) ∧
  (((0 : Vert) ∈ S ∧ (3 : Vert) ∈ S ∧ (4 : Vert) ∈ S) ∨
   ((0 : Vert) ∈ T ∧ (3 : Vert) ∈ T ∧ (4 : Vert) ∈ T))

/-- Exhaustive calculation: no two proper closed vertex sets freely
cover all five closure triples. Does not assert semantic U-irreducibility
until the higher-level encoding bridge is proved. -/
theorem no_closed_two_side_cover :
    ∀ (S T : Finset Vert), Closed S → Closed T →
      S ∪ T = all → TupleCover S T → S = all ∨ T = all := by
  intro S T hS hT _ hTuples
  have hall :
      (((0 : Vert) ∈ S ∧ (1 : Vert) ∈ S ∧ (2 : Vert) ∈ S ∧
        (3 : Vert) ∈ S ∧ (4 : Vert) ∈ S) ∨
       ((0 : Vert) ∈ T ∧ (1 : Vert) ∈ T ∧ (2 : Vert) ∈ T ∧
        (3 : Vert) ∈ T ∧ (4 : Vert) ∈ T)) := by
    rcases hS with ⟨hs01, hs02, hs13, hs24, hs34⟩
    rcases hT with ⟨ht01, ht02, ht13, ht24, ht34⟩
    rcases hTuples with ⟨hX, hY, hZ, hW⟩
    rcases hX with ⟨sx0, sx1, sx2⟩ | ⟨tx0, tx1, tx2⟩
    · rcases hW with ⟨sw0, sw3, sw4⟩ | ⟨tw0, tw3, tw4⟩
      · exact Or.inl ⟨sx0, sx1, sx2, sw3, sw4⟩
      · rcases hY with ⟨sy0, sy1, sy3⟩ | ⟨ty0, ty1, ty3⟩
        · rcases hZ with ⟨sz0, sz2, sz4⟩ | ⟨tz0, tz2, tz4⟩
          · exact Or.inl ⟨sx0, sx1, sx2, sy3, sz4⟩
          · exact Or.inr ⟨tw0, ht02 tw0 tz2, tz2, tw3, tw4⟩
        · rcases hZ with ⟨sz0, sz2, sz4⟩ | ⟨tz0, tz2, tz4⟩
          · exact Or.inr ⟨tw0, ty1, ht01 tw0 ty1, tw3, tw4⟩
          · exact Or.inr ⟨ty0, ty1, tz2, ty3, tz4⟩
    · rcases hW with ⟨sw0, sw3, sw4⟩ | ⟨tw0, tw3, tw4⟩
      · rcases hY with ⟨sy0, sy1, sy3⟩ | ⟨ty0, ty1, ty3⟩
        · rcases hZ with ⟨sz0, sz2, sz4⟩ | ⟨tz0, tz2, tz4⟩
          · exact Or.inl ⟨sy0, sy1, sz2, sy3, sz4⟩
          · exact Or.inl ⟨sw0, sy1, hs01 sw0 sy1, sw3, sw4⟩
        · rcases hZ with ⟨sz0, sz2, sz4⟩ | ⟨tz0, tz2, tz4⟩
          · exact Or.inl ⟨sw0, hs02 sw0 sz2, sz2, sw3, sw4⟩
          · exact Or.inr ⟨tx0, tx1, tx2, ty3, tz4⟩
      · exact Or.inr ⟨tx0, tx1, tx2, tw3, tw4⟩
  rcases hall with h | h
  · left
    apply Finset.eq_univ_of_forall
    intro x
    fin_cases x <;> tauto
  · right
    apply Finset.eq_univ_of_forall
    intro x
    fin_cases x <;> tauto

private def step (S : Finset Vert) : Finset Vert :=
  S ∪ (if (0 : Vert) ∈ S ∧ (1 : Vert) ∈ S then {2} else ∅) ∪
      (if (0 : Vert) ∈ S ∧ (2 : Vert) ∈ S then {1} else ∅) ∪
      (if (1 : Vert) ∈ S ∧ (3 : Vert) ∈ S then {0} else ∅) ∪
      (if (2 : Vert) ∈ S ∧ (4 : Vert) ∈ S then {0} else ∅) ∪
      (if (3 : Vert) ∈ S ∧ (4 : Vert) ∈ S then {0} else ∅)

private def hull (S : Finset Vert) : Finset Vert :=
  step (step (step (step (step S))))

private def IsIrreducibleSeed (S : Finset Vert) : Prop :=
  ¬ ((1 : Vert) ∈ S ∧ (4 : Vert) ∈ S) ∧
  ¬ ((2 : Vert) ∈ S ∧ (3 : Vert) ∈ S)

/-- No ordinary irreducible induced seed generates all five vertices. -/
private theorem mem_step_three (S : Finset Vert) :
    (3 : Vert) ∈ step S ↔ (3 : Vert) ∈ S := by
  classical
  simp only [step, Finset.mem_union]
  split_ifs <;> simp_all

private theorem mem_step_four (S : Finset Vert) :
    (4 : Vert) ∈ step S ↔ (4 : Vert) ∈ S := by
  classical
  simp only [step, Finset.mem_union]
  split_ifs <;> simp_all

private theorem no12_step (S : Finset Vert)
    (h1 : (1 : Vert) ∉ S) (h2 : (2 : Vert) ∉ S) :
    (1 : Vert) ∉ step S ∧ (2 : Vert) ∉ step S := by
  classical
  simp only [step, Finset.mem_union]
  split_ifs <;> simp_all [h1, h2]

theorem irreducible_seed_not_generating :
    ∀ S : Finset Vert, IsIrreducibleSeed S → hull S ≠ all := by
  intro S hSeed hFull
  have h3 : (3 : Vert) ∈ S := by
    have h : (3 : Vert) ∈ hull S := by rw [hFull]; simp [all]
    simpa only [hull, mem_step_three] using h
  have h4 : (4 : Vert) ∈ S := by
    have h : (4 : Vert) ∈ hull S := by rw [hFull]; simp [all]
    simpa only [hull, mem_step_four] using h
  have h1 : (1 : Vert) ∉ S := by
    intro h
    exact hSeed.1 ⟨h, h4⟩
  have h2 : (2 : Vert) ∉ S := by
    intro h
    exact hSeed.2 ⟨h, h3⟩
  have ha := no12_step S h1 h2
  have hb := no12_step (step S) ha.1 ha.2
  have hc := no12_step (step (step S)) hb.1 hb.2
  have hd := no12_step (step (step (step S))) hc.1 hc.2
  have he := no12_step (step (step (step (step S)))) hd.1 hd.2
  have hNo : (1 : Vert) ∉ hull S := he.1
  apply hNo
  rw [hFull]
  simp [all]

theorem generating_support_card_ge_three :
    ∀ S : Finset Vert, hull S = all → 3 ≤ S.card := by
  decide

theorem two_three_vertex_generators :
    hull ({1, 3, 4} : Finset Vert) = all ∧
    hull ({2, 3, 4} : Finset Vert) = all := by
  decide

end StructuralRamsey.RelStructure.FiniteSeedObstruction

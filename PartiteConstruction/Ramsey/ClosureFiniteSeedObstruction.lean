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
  decide

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
theorem irreducible_seed_not_generating :
    ∀ S : Finset Vert, IsIrreducibleSeed S → hull S ≠ all := by
  decide

theorem generating_support_card_ge_three :
    ∀ S : Finset Vert, hull S = all → 3 ≤ S.card := by
  decide

theorem two_three_vertex_generators :
    hull ({1, 3, 4} : Finset Vert) = all ∧
    hull ({2, 3, 4} : Finset Vert) = all := by
  decide

end StructuralRamsey.RelStructure.FiniteSeedObstruction

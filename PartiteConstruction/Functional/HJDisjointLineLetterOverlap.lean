import PartiteConstruction.Functional.HJLineOverlapDichotomy
import PartiteConstruction.Functional.HJCoordinateShadowSharpness

/-!
# Track D: exact irreducible overlap control for disjoint HJ parameters

For two actual native Hales--Jewett lines with no common parameter
coordinate, their images can meet only in one FULL A-letter copy of
the first line. This is stronger than saying their common projected
support has small size: the source FULL A-copy is explicitly given
by one constant letter at a parameter coordinate of the first line.

The theorem works with genuinely multivalued but part-transversal
functions, arbitrary positive/nullary arities, and exact source
carriers. No closure hull is inserted and no target B-tree completion
is assumed. In a history with three or more lines, pairwise control
does not synchronize all relative target completions, so the C7
obstruction remains relevant.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.HalesJewett
universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- A pair of native HJ lines with DISJOINT parameter sets has
intersection supported inside a single actual full A-letter copy.

The selected letter is obtained at one parameter coordinate of W₁
where W₂ has a constant letter. No assumptions on original weak
homomorphisms are required for this geometric statement. -/
theorem disjoint_lines_overlap_in_full_letter
    (W₁ W₂ : Line (Letter A B) N)
    (hDisjoint : ∀ i : Fin N,
      W₁.symbol i = .parameter → W₂.symbol i ≠ .parameter) :
    ∃ e : Letter A B,
      (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
        Set.range (fun p : P => lineMap W₁ (e p)) := by
  obtain ⟨i, h₁⟩ := W₁.hasParameter
  cases h₂ : W₂.symbol i with
  | parameter =>
      exact ((hDisjoint i h₁) h₂).elim
  | const e =>
      exact ⟨e, line_range_inter_subset_letter W₁ W₂ i e h₁ h₂⟩

/-- In the complement of the common-parameter case, the exact
one-sided full-letter bound is available *without* asking for any
rooted strict tree witness. This is the useful geometrical piece of
the still-open multi-line history induction. -/
theorem line_pair_shared_parameter_or_full_letter
    (W₁ W₂ : Line (Letter A B) N) :
    (∃ i : Fin N, W₁.symbol i = .parameter ∧
      W₂.symbol i = .parameter) ∨
    (∃ e : Letter A B,
      (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
        Set.range (fun p : P => lineMap W₁ (e p))) := by
  classical
  by_cases h : ∃ i : Fin N,
      W₁.symbol i = .parameter ∧ W₂.symbol i = .parameter
  · exact Or.inl h
  · right
    apply disjoint_lines_overlap_in_full_letter W₁ W₂
    intro i h₁ h₂
    exact h ⟨i, h₁, h₂⟩

end StructuralRamsey.FunctionalPartite.Induced

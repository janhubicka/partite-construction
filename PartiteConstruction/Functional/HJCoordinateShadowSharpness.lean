import PartiteConstruction.Functional.EHNCommonParameterLineFamily
import PartiteConstruction.Functional.HJLineOverlapDichotomy

/-!
# Track D: sharp criterion for an HJ coordinate to split a whole support

The earlier positive history theorem constructs a strict functional
B-tree witness when all full support line attachments are split by
one Hales--Jewett evaluation coordinate. Here we verify that the
common-parameter condition is not just a sufficient convenience:
whenever one old part contains two distinct support vertices, a
coordinate evaluation splits the ENTIRE old support of a line if
and only if that coordinate is a parameter of the line.

This is true for genuine set-valued, part-transversal functional
systems; the proof needs only the precise coordinatewise HJ line map.
No old test is enlarged by closure and no full-fibre projection is
assumed. The conclusion is about COORDINATE shadows only, not about
all possible history-dependent EHN shadows or strict relative
B-tree target extensions.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.HalesJewett
universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- A coordinate evaluation splits a complete native HJ line
whenever that coordinate carries a parameter. -/
theorem line_coordinate_splits_of_parameter
    (W : Line (Letter A B) N) (i : Fin N)
    (hi : W.symbol i = .parameter) :
    ∀ z : V, (lineMap W z).coord i = z := by
  intro z
  simp [lineMap, hi]

/-- In a genuine old support with two distinct vertices in one part,
coordinate splitting FORCES the line's coordinate to be a parameter.
A constant letter would identify those two vertices. -/
theorem line_parameter_of_coordinate_splits
    (W : Line (Letter A B) N) (i : Fin N)
    (x y : V) (hPart : B.part x = B.part y) (hne : x ≠ y)
    (hSplit : ∀ z : V, (lineMap W z).coord i = z) :
    W.symbol i = .parameter := by
  cases h : W.symbol i with
  | parameter => exact h
  | const e =>
      have hx : e (B.part x) = x := by
        simpa [lineMap, h] using hSplit x
      have hy : e (B.part y) = y := by
        simpa [lineMap, h] using hSplit y
      apply (hne (hx.symm.trans ((congrArg e hPart).trans hy))).elim

/-- Under a nontrivial part fibre, the parameter-coordinate criterion
for splitting the ENTIRE line is an exact equivalence. -/
theorem line_coordinate_splits_iff_parameter
    (W : Line (Letter A B) N) (i : Fin N)
    (x y : V) (hPart : B.part x = B.part y) (hne : x ≠ y) :
    (∀ z : V, (lineMap W z).coord i = z) ↔
      W.symbol i = .parameter := by
  constructor
  · exact line_parameter_of_coordinate_splits W i x y hPart hne
  · exact line_coordinate_splits_of_parameter W i

/-- For a finite list of genuine Hales--Jewett line attachments, the
same evaluation coordinate splits ALL selected support maps if and
only if it is a COMMON parameter coordinate. This makes the scope
of the validated positive family theorem exact. -/
theorem line_family_coordinate_splits_iff_common_parameter
    (lines : List (Line (Letter A B) N)) (i : Fin N)
    (x y : V) (hPart : B.part x = B.part y) (hne : x ≠ y) :
    (∀ W ∈ lines, ∀ z : V, (lineMap W z).coord i = z) ↔
      (∀ W ∈ lines, W.symbol i = .parameter) := by
  constructor
  · intro h W hW
    exact (line_coordinate_splits_iff_parameter
      W i x y hPart hne).mp (h W hW)
  · intro h W hW
    exact (line_coordinate_splits_iff_parameter
      W i x y hPart hne).mpr (h W hW)

/-- Two lines with disjoint parameter sets cannot both have their
entire support split by the SAME coordinate evaluation, as soon as
the support has a nontrivial part fibre.

This excludes a universal coordinate shadow, not an arbitrary EHN
retraction nor a compatible ROOTED target completion. -/
theorem disjoint_lines_no_common_coordinate_shadow
    (W₁ W₂ : Line (Letter A B) N)
    (x y : V) (hPart : B.part x = B.part y) (hne : x ≠ y)
    (hDisjoint : ∀ i : Fin N,
      ¬ (W₁.symbol i = .parameter ∧ W₂.symbol i = .parameter)) :
    ¬ ∃ i : Fin N,
      (∀ z : V, (lineMap W₁ z).coord i = z) ∧
      (∀ z : V, (lineMap W₂ z).coord i = z) := by
  rintro ⟨i, h₁, h₂⟩
  exact hDisjoint i
    ⟨(line_coordinate_splits_iff_parameter
        W₁ i x y hPart hne).mp h₁,
      (line_coordinate_splits_iff_parameter
        W₂ i x y hPart hne).mp h₂⟩

end StructuralRamsey.FunctionalPartite.Induced

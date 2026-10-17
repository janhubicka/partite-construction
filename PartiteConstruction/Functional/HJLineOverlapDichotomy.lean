import PartiteConstruction.Functional.TransversalEmbeddingEqualizer

/-!
# Pairwise intersections of genuine functional Hales--Jewett lines

An actual Hales--Jewett line has a parameter coordinate. For two lines
W₁ and W₂, inspect ANY parameter coordinate i of W₁.

* If i is also a parameter of W₂, a point in the two line ranges
  must have the SAME input vertex x in both parameterizations.
  The intersection is the image under W₁ of the exact pointwise
  agreement root {x | W₁ x = W₂ x}. This root is function-closed
  by per-fibre output transversality.

* If i is constant with letter e in W₂, every point in the
  intersection is already in the FULL A-copy W₁ ∘ e. Indeed
  equality of the i-th coordinate forces x=e(part x).

No singleton-function hypothesis, no generated closure of a weak test,
and no global total-fibre projection is needed. These are exact
geometric restrictions on TWO overlapping HJ lines. They do NOT imply
that three or more line attachments have a common compatible B-tree:
the seven-cycle audit gives an explicit counterexample.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- If two HJ lines share a parameter coordinate, equality of
their images forces equality of the two source vertices. -/
theorem lineMap_eq_source_of_common_parameter
    (W₁ W₂ : Line (Letter A B) N)
    (i : Fin N)
    (h₁ : W₁.symbol i = .parameter)
    (h₂ : W₂.symbol i = .parameter)
    {x y : V} (h : lineMap W₁ x = lineMap W₂ y) :
    x = y := by
  have hc := congrArg (fun z : Vertex B N => z.coord i) h
  simpa only [lineMap, h₁, h₂] using hc

/-- With a common parameter coordinate, the EXACT overlap of two
line ranges is precisely the image of the agreement root in the
old selected support. No closure hull of the tested vertices occurs. -/
theorem line_range_inter_eq_agreement_image
    (W₁ W₂ : Line (Letter A B) N)
    (i : Fin N)
    (h₁ : W₁.symbol i = .parameter)
    (h₂ : W₂.symbol i = .parameter) :
    (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) =
      (lineMap W₁) ''
        {x : V | lineMap W₁ x = lineMap W₂ x} := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have hxy : x = y :=
      lineMap_eq_source_of_common_parameter W₁ W₂ i h₁ h₂ hy.symm
    subst y
    exact ⟨x, hy.symm, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨x, hx.symm⟩⟩

/-- In the parameter/constant case, every shared image vertex
comes from the specified FULL A-letter on the parameter line.
Output transversality is not required for this purely geometric step. -/
theorem lineMap_eq_letter_of_parameter_const
    (W₁ W₂ : Line (Letter A B) N)
    (i : Fin N) (e : Letter A B)
    (h₁ : W₁.symbol i = .parameter)
    (h₂ : W₂.symbol i = .const e)
    {x y : V} (h : lineMap W₁ x = lineMap W₂ y) :
    x = e (B.part x) := by
  have hp : B.part x = B.part y :=
    congrArg (fun z : Vertex B N => z.part) h
  have hc := congrArg (fun z : Vertex B N => z.coord i) h
  have hxy : x = e (B.part y) := by
    simpa only [lineMap, h₁, h₂] using hc
  exact hxy.trans (congrArg e hp.symm)

/-- A parameter/constant overlap is contained in an ACTUAL full
A-copy of the first HJ line, not merely in an abstract A-labelled
weak image. -/
theorem line_range_inter_subset_letter
    (W₁ W₂ : Line (Letter A B) N)
    (i : Fin N) (e : Letter A B)
    (h₁ : W₁.symbol i = .parameter)
    (h₂ : W₂.symbol i = .const e) :
    (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
      Set.range (fun p : P => lineMap W₁ (e p)) := by
  rintro z ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
  have hx : x = e (B.part x) :=
    lineMap_eq_letter_of_parameter_const W₁ W₂ i e h₁ h₂ hy.symm
  exact ⟨B.part x, congrArg (lineMap W₁) hx.symm⟩

/-- An exhaustive and constructive overlap dichotomy for ANY pair of
native HJ lines. Either a common parameter coordinates both copies
of one exact closed agreement root, or the pairwise overlap lies
inside one full A-letter copy. -/
theorem line_overlap_closedRoot_or_letter
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W₁ W₂ : Line (Letter A B) N) :
    (∃ i : Fin N,
        W₁.symbol i = .parameter ∧
        W₂.symbol i = .parameter ∧
        B.toStructure.IsClosed
          {x : V | lineMap W₁ x = lineMap W₂ x} ∧
        (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) =
          (lineMap W₁) ''
            {x : V | lineMap W₁ x = lineMap W₂ x}) ∨
    (∃ e : Letter A B,
        (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
          Set.range (fun p : P => lineMap W₁ (e p))) := by
  obtain ⟨i, hi⟩ := W₁.hasParameter
  cases hj : W₂.symbol i with
  | parameter =>
      exact Or.inl ⟨i, hi, hj,
        line_agreement_isClosed hB W₁ W₂,
        line_range_inter_eq_agreement_image W₁ W₂ i hi hj⟩
  | const e =>
      exact Or.inr ⟨e,
        line_range_inter_subset_letter W₁ W₂ i e hi hj⟩

end StructuralRamsey.FunctionalPartite.Induced

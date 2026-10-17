import PartiteConstruction.Functional.HJLineOverlapDichotomy

/-!
# Two Hales--Jewett lines overlapping in every part

An especially rigid case of the exact pairwise-overlap dichotomy:
suppose two genuine Hales--Jewett LINE ranges meet in EVERY control
part p:P. If the line words differ, then their overlap lies in a
FULL A-letter copy of at least one of the lines.

Indeed, if neither line ever has a parameter where the other is
constant, their parameter positions coincide. At every common
constant coordinate the two letters agree at every p because the
lines share a vertex of each part, hence the letters coincide as
full partite embeddings. The line words would then be equal.

This exact argument uses no closure generation, cardinality bound,
singleton-valued function assumption, or false multi-line union
property. For A=K₂, meeting in both A-parts is the hypothesis.
It is one possible input to a MAXIMAL-projection-rank analysis:
a tested vertex set with injective part map has at most one vertex
in each control part. No claim of compatible strict B-tree
completions is made here.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- Distinct native HJ line words whose ranges overlap in EVERY part
have their exact common range contained in an actual full A-copy
of one of those line maps. The side (W₁ or W₂) is allowed to depend
on the witness for differing parameter positions. -/
theorem line_fullPartOverlap_in_letter
    (W₁ W₂ : Line (Letter A B) N)
    (hDistinct : W₁.symbol ≠ W₂.symbol)
    (hCover : ∀ p : P, ∃ z : Vertex B N,
      z ∈ (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ∧
      z.part = p) :
    (∃ e : Letter A B,
      (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
        Set.range (fun p : P => lineMap W₁ (e p))) ∨
    (∃ e : Letter A B,
      (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) ⊆
        Set.range (fun p : P => lineMap W₂ (e p))) := by
  have hMismatch :
      ∃ i : Fin N,
        (∃ e : Letter A B,
          W₁.symbol i = .parameter ∧ W₂.symbol i = .const e) ∨
        (∃ e : Letter A B,
          W₂.symbol i = .parameter ∧ W₁.symbol i = .const e) := by
    by_contra hNo
    apply hDistinct
    funext i
    cases h₁ : W₁.symbol i with
    | parameter =>
        cases h₂ : W₂.symbol i with
        | parameter =>
            simp [h₁, h₂]
        | const e =>
            exact (hNo ⟨i, Or.inl ⟨e, h₁, h₂⟩⟩).elim
    | const e₁ =>
        cases h₂ : W₂.symbol i with
        | parameter =>
            exact (hNo ⟨i, Or.inr ⟨e₁, h₂, h₁⟩⟩).elim
        | const e₂ =>
            have he : e₁ = e₂ := by
              apply FunctionalPartite.Embedding.ext
              intro p
              obtain ⟨z, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hz⟩ := hCover p
              have hxp : B.part x = p := by
                calc
                  B.part x = (lineMap W₁ x).part := rfl
                  _ = z.part := congrArg (fun q : Vertex B N => q.part) hx
                  _ = p := hz
              have hyp : B.part y = p := by
                calc
                  B.part y = (lineMap W₂ y).part := rfl
                  _ = z.part := congrArg (fun q : Vertex B N => q.part) hy
                  _ = p := hz
              have hc := congrArg (fun q : Vertex B N => q.coord i)
                (hx.trans hy.symm)
              have hexy : e₁ (B.part x) = e₂ (B.part y) := by
                simpa only [lineMap, h₁, h₂] using hc
              simpa only [hxp, hyp] using hexy
            simp [h₁, h₂, he]
  obtain ⟨i, h⟩ := hMismatch
  rcases h with ⟨e, hvar, hconst⟩ | ⟨e, hvar, hconst⟩
  · exact Or.inl ⟨e,
      line_range_inter_subset_letter W₁ W₂ i e hvar hconst⟩
  · have hSub :
        (Set.range (lineMap W₂) ∩ Set.range (lineMap W₁)) ⊆
          Set.range (fun p : P => lineMap W₂ (e p)) :=
      line_range_inter_subset_letter W₂ W₁ i e hvar hconst
    exact Or.inr ⟨e, fun z hz => hSub ⟨hz.2, hz.1⟩⟩

end StructuralRamsey.FunctionalPartite.Induced

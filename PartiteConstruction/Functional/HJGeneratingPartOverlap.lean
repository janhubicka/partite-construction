import PartiteConstruction.Functional.HJLineOverlapDichotomy
import PartiteConstruction.Functional.TransversalEmbeddingGenerators

/-!
# Functional Hales--Jewett overlaps controlled by generated parts

The full-part overlap rigidity can be strengthened: it suffices for
two genuine Hales--Jewett lines to share at least one vertex in EVERY
part of a subset G that FUNCTION-GENERATES the control structure A.

If their words differ, there is a parameter/constant mismatch and the
whole pairwise overlap lies inside one actual FULL A-letter copy.

The key new fact is that two constant letters whose values agree on G
are identical on the ENTIRE A: the partite target has transversal
set-valued function fibres, so the exact embedding equalizer is closed
and contains the functional closure of G.

No singleton-valuedness, extra root vertices, or arbitrary-stage
strict B-tree extension assumption enters this statement. It remains
pairwise; its conclusion does NOT synchronize overlaps with a family
of three or more HJ line attachments.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.HalesJewett
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- For two different actual line words, meeting in every part of a
function-generating subset already forces their entire overlap into
one full A-copy of one of the two line ranges. -/
theorem line_generatingPartOverlap_in_letter
    (W₁ W₂ : Line (Letter A B) N)
    (G : Set P)
    (hGen : A.functionClosure G = Set.univ)
    (hDistinct : W₁.symbol ≠ W₂.symbol)
    (hCover : ∀ p : P, p ∈ G →
      ∃ z : Vertex B N,
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
              apply FunctionalPartite.Embedding.eq_of_agree_on_generators
                  e₁ e₂ G hGen
              intro p hp
              obtain ⟨z, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hz⟩ := hCover p hp
              have hxp : B.part x = p := by
                calc
                  B.part x = (lineMap W₁ x).part := rfl
                  _ = z.part :=
                    congrArg (fun q : Vertex B N => q.part) hx
                  _ = p := hz
              have hyp : B.part y = p := by
                calc
                  B.part y = (lineMap W₂ y).part := rfl
                  _ = z.part :=
                    congrArg (fun q : Vertex B N => q.part) hy
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

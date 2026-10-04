import PartiteConstruction.Iterated.ProjectedHistoryLocalTreeLike

/-! # Projected histories are stronger than ordinary tree completability

For the identity projection, a projected-history witness may be asked to
remember the singleton subset of every tested vertex.  Equality of two target
values must then preserve membership in each singleton, so the witness map is
injective on the whole test.

Thus `ProjectedHistoryLocallyTreeLike` contains genuinely more information
than `LocallyTreeCompletable`: the latter permits collapses on reducible
pieces, while the former can be queried so that no tested vertices collapse.
This is the exact strength gap that remains in the outer sparsening
iteration after the local tree-completion theorem.
-/
namespace StructuralRamsey.RelStructure.ProjectedHistoryLocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}

/-- At identity projection, projected histories give an injective
homomorphism-embedding witness on every tested finite set. -/
theorem injectiveWitness_identity
    {n : ℕ}
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id n)
    (S : Finset P) (hS : S.card ≤ n) :
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set P) → Z,
        (D.induce (↑S : Set P)).IsHomomorphismEmbedding Target f ∧
        Function.Injective f := by
  classical
  let history : List (Set P) :=
    S.toList.map (fun x => ({x} : Set P))
  obtain ⟨Z, Target, hTree, f, hf, _hPart, hHist⟩ :=
    h S hS history
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro x y hxy
  let H : Set P := {x.1}
  have hxList : x.1 ∈ S.toList := by
    simpa using x.2
  have hH : H ∈ history := by
    simp [history, H, hxList]
  have hmem := hHist H hH x y hxy
  have hy : y.1 = x.1 := by
    have : y.1 ∈ H := hmem.mp (by simp [H])
    simpa [H] using this
  apply Subtype.ext
  exact hy.symm

/-- Consequently, identity projected-history coherence supplies injective
finite tree completions, not merely ordinary homomorphism-embedding
completions. -/
theorem injectiveCompletion_identity
    {n : ℕ}
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id n) :
    ∀ S : Finset P, S.card ≤ n →
      ∃ (Z : Type v) (Target : RelStructure L Z),
        TreeAmalgam B Z Target ∧
        ∃ f : ↥(↑S : Set P) → Z,
          (D.induce (↑S : Set P)).IsHomomorphismEmbedding Target f ∧
          Function.Injective f :=
  fun S hS => injectiveWitness_identity h S hS

end StructuralRamsey.RelStructure.ProjectedHistoryLocallyTreeLike

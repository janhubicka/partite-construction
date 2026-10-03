import PartiteConstruction.Functional.FunctionDomains
import PartiteConstruction.Ramsey.Basic

/-! # Root pruning of ordinary Ramsey witnesses

An ordinary relational Ramsey witness in the domain-expanded graph language
need not satisfy output -> domain/root.  We can repair it by deleting exactly
those function-output tuples whose input tuple is not declared to be in the
corresponding domain relation.

Every embedding from a root-correct source survives this pruning.  Hence a
Ramsey arrow A -> B in the unpruned witness descends to the pruned witness
whenever both A and B are root-correct.
-/
namespace StructuralRamsey.RelStructure

open Structure

universe u v w z
variable {L : Language.{u}}
variable {U : Type v} {V : Type w} {W : Type z}

/-- Delete function-output tuples which do not carry the corresponding
domain/root relation.  All ordinary relations, including domain relations,
are left unchanged. -/
def rootPrune
    (D : RelStructure L.withFunctionDomains.graph W) :
    RelStructure L.withFunctionDomains.graph W where
  rel
    | .inl R, x => D.rel (.inl R) x
    | .inr F, t =>
        D.rel (.inr F) t ∧
        D.rel (.inl (.inr F))
          (fun i => t (Fin.castSucc i))

/-- Root pruning enforces output -> domain by construction. -/
theorem rootPrune_outputImpliesDomain
    (D : RelStructure L.withFunctionDomains.graph W) :
    (rootPrune D).OutputImpliesDomain := by
  intro F x y hy
  exact hy.2

namespace Embedding

/-- An embedding from a root-correct source survives root pruning of the
target. -/
def toRootPrune
    {A : RelStructure L.withFunctionDomains.graph U}
    {D : RelStructure L.withFunctionDomains.graph W}
    (hA : A.OutputImpliesDomain)
    (e : Embedding A D) :
    Embedding A (rootPrune D) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        exact e.map_rel_iff (.inl R) x
    | inr F =>
        let args : Fin (L.withFunctionDomains.funcArity F) → U :=
          fun i => x (Fin.castSucc i)
        constructor
        · intro hx
          exact
            (e.map_rel_iff (.inr F) x).mp hx.1
        · intro hx
          have hout :
              D.rel (.inr F) (e ∘ x) :=
            (e.map_rel_iff (.inr F) x).mpr hx
          have hrootA :
              A.rel (.inl (.inr F)) args :=
            hA F args
              (x (Fin.last
                (L.withFunctionDomains.funcArity F))) hx
          have hrootD0 :
              D.rel (.inl (.inr F)) (e ∘ args) :=
            (e.map_rel_iff
              (.inl (.inr F)) args).mpr hrootA
          have hargs :
              (fun i =>
                (e ∘ x) (Fin.castSucc i)) =
                e ∘ args := by
            funext i
            rfl
          refine ⟨hout, ?_⟩
          rw [hargs]
          exact hrootD0

@[simp] theorem toRootPrune_apply
    {A : RelStructure L.withFunctionDomains.graph U}
    {D : RelStructure L.withFunctionDomains.graph W}
    (hA : A.OutputImpliesDomain)
    (e : Embedding A D) (x : U) :
    e.toRootPrune hA x = e x := rfl

end Embedding

/-- Ordinary Ramsey arrows descend to the root-pruned witness for root-correct
source and target structures. -/
theorem arrow_rootPrune
    (A : RelStructure L.withFunctionDomains.graph U)
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph W)
    (hAroot : A.OutputImpliesDomain)
    (hBroot : B.OutputImpliesDomain)
    (κ : Type*)
    (hRamsey : StructuralRamsey.Arrow A B D κ) :
    StructuralRamsey.Arrow A B (rootPrune D) κ := by
  intro χ
  let θ : Embedding A D → κ :=
    fun e => χ (e.toRootPrune hAroot)
  obtain ⟨f, hf⟩ := hRamsey θ
  let fg : Embedding B (rootPrune D) :=
    f.toRootPrune hBroot
  refine ⟨fg, ?_⟩
  intro e₁ e₂
  have hm := hf e₁ e₂
  have hcomp₁ :
      (f.comp e₁).toRootPrune hAroot =
        fg.comp e₁ := by
    apply Embedding.ext
    intro x
    rfl
  have hcomp₂ :
      (f.comp e₂).toRootPrune hAroot =
        fg.comp e₂ := by
    apply Embedding.ext
    intro x
    rfl
  change
    χ ((f.comp e₁).toRootPrune hAroot) =
      χ ((f.comp e₂).toRootPrune hAroot) at hm
  rw [hcomp₁, hcomp₂] at hm
  exact hm

end StructuralRamsey.RelStructure

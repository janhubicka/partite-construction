import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019
import PartiteConstruction.Functional.WholeMaskRelativeClosure2019
import PartiteConstruction.Functional.WholeMaskActiveRootExtraction
import PartiteConstruction.Ramsey.ClosureUSize2019

/-!
# Every OLD complete positive output lies in its actual input U-hull

Full-root tag normality identifies the entire arbitrary tagged target
with the canonical tag expansion of its OWN OLD relational reduct.
Under correct OLD graph-root validity, a complete OLD output tuple
therefore becomes a fresh closure tuple over the full induced OLD
input root. Consequently each output vertex lies in the U-closure
of precisely the original distinct input vertices.

This hull is used only as a protected target-side witness for future
cross-pattern output comparisons. No exact weak source test, weak
projection, or induction-size parameter is replaced by a closure hull.
Defined-empty outputs add no output vertices and nullary inputs require
the separate nullary-root reduction.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V : Type v}

/-- Normality makes a tagged target LITERALLY the canonical complete
mask expansion of its own OLD reduct, without changing its carrier. -/
theorem WholeMaskTagNormal.eqCanonical
    {C : RelStructure (L.wholeMaskTagLanguage P) V}
    (h : WholeMaskTagNormal C) :
    C = wholeMaskTagExpansion (wholeMaskTagReduct C) := by
  apply rel_injective
  funext R t
  cases R with
  | inl R => rfl
  | inr p => exact propext (h p t)

/-- Every old complete-output relation tuple in a normal target with
valid domain roots forces each of its positive outputs into the exact
2019 U-closure of its DISTINCT primitive input-root vertex set.
The primitive function must have positive arity, but its arguments
may repeat. The mask length is positive whenever an output j exists. -/
theorem WholeMaskTagNormal.completeOutput_mem_inputHull
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (hNormal : WholeMaskTagNormal C)
    (hValid : HasValidCompleteMaskDomains (wholeMaskTagReduct C))
    (hPos : L.PositiveFuncArity)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (t : Fin (p.rootSize + q.size) → V)
    (hOld : (wholeMaskTagReduct C).rel
      (.inr (.inr (p,q))) t)
    (j : Fin q.size) :
    t (Fin.natAdd p.rootSize j) ∈
      UClosureHull (L.wholeMaskClosureRules P) C
        (Set.range (fun i : Fin p.rootSize =>
          t (Fin.castAdd q.size i))) := by
  classical
  have hpPos : 0 < p.rootSize := by
    by_contra hn
    have hpZero : p.rootSize = 0 := Nat.eq_zero_of_not_pos hn
    have k : Fin p.rootSize := p.argMap ⟨0, hPos p.symbol⟩
    exact Fin.elim0 (hpZero ▸ k)
  have hqPos : 0 < q.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  obtain ⟨hInj, hDom⟩ := hValid p q t hOld
  let E := wholeMaskTagReduct C
  let root : Fin p.rootSize → V :=
    fun i => t (Fin.castAdd q.size i)
  let pat : Language.WholeMaskRootPattern L P :=
    Language.WholeMaskRootPattern.ofActiveDomain
      E p q hpPos hqPos root hDom
  have hCanonical : (wholeMaskTagExpansion E).rel (.inr pat) t := by
    change E.rel (.inr (.inr (p,q))) t ∧
      ∃ g : Embedding pat.root E,
        ∀ i : Fin p.rootSize,
          t (Fin.castAdd q.size i) = g i
    refine ⟨hOld,
      Language.WholeMaskRootPattern.ofActiveDomain_embedding
        E p q hpPos hqPos root hInj hDom, ?_⟩
    intro i
    rfl
  have hTag : C.rel (.inr pat) t :=
    (hNormal pat t).mpr hCanonical
  let H : Set V :=
    UClosureHull (L.wholeMaskClosureRules P) C (Set.range root)
  have hH : IsUSubstructure (L.wholeMaskClosureRules P) C H :=
    UClosureHull_isUSubstructure
      (L.wholeMaskClosureRules P) C (Set.range root)
  have hRoot : ∀ i : Fin pat.closureRule.rootSize,
      t (i.castLE pat.closureRule.rootLE) ∈ H := by
    intro i
    have hEq : i.castLE pat.closureRule.rootLE =
        Fin.castAdd q.size i := by
      apply Fin.ext
      rfl
    rw [hEq]
    exact subset_UClosureHull
      (L.wholeMaskClosureRules P) C (Set.range root)
      ⟨i, rfl⟩
  exact hH pat.closureRule ⟨pat, rfl⟩
    t hTag hRoot (Fin.natAdd p.rootSize j)

end StructuralRamsey.RelStructure

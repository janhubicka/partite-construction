import PartiteConstruction.Functional.PatternTagIdentity2019
import PartiteConstruction.Ramsey.ClosureUSize2019
import PartiteConstruction.Functional.PatternCompleteRootExtraction2019

/-!
# Function outputs belong to the U-closure of their exact input vertices

In a NORMAL final tagged Picture, a valid old function-output tuple
with an active positive root necessarily has a FRESH closure tag:
its full OLD root pattern is extracted from the exact distinct inputs.
A relative U-substructure containing those inputs must therefore
contain that output. In particular the output belongs to the
UClosureHull of the original input tuple.

The source generators and their size do NOT change. This is the
closure mechanism needed to place *all* incompatible candidate
outputs for the same primitive input in ONE protected U-closed
test before applying B-copy coverage and singleton-valuedness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every correctly tagged old output of a positive-root pattern
lies in the U-closure of the SAME original distinct input vertices.
No U-closedness of the full ambient C is needed for this inclusion. -/
theorem PatternTagNormal.old_output_mem_generatedHull
    (C : RelStructure (L.patternTag) V)
    (hNormal : PatternTagNormal C)
    (p : Language.FunctionInputPattern L) (hpos : 0 < p.rootSize)
    (t : Fin (p.rootSize + 1) → V)
    (hOld : (patternTagReduct C).rel (.inr (.inr p)) t)
    (hinj : Function.Injective
      (fun i : Fin p.rootSize => t i.castSucc))
    (hDom : (patternTagReduct C).rel (.inr (.inl p))
      (fun i : Fin p.rootSize => t i.castSucc)) :
    t (Fin.last p.rootSize) ∈
      UClosureHull L.patternClosureRules C
        (Set.range (fun i : Fin p.rootSize => t i.castSucc)) := by
  let root : Fin p.rootSize → V := fun i => t i.castSucc
  let q : Language.FunctionRootPattern L :=
    Language.FunctionRootPattern.ofActiveDomain
      (patternTagReduct C) p hpos root hDom
  have hOldTag :
      (patternTagExpansion (patternTagReduct C)).rel (.inr q) t :=
    patternTagExpansion_tag_of_valid_old_output
      (patternTagReduct C) p hpos t hOld hinj hDom
  have hTag : C.rel (.inr q) t :=
    (hNormal q t).mpr hOldTag
  let H : Set V := UClosureHull L.patternClosureRules C (Set.range root)
  have hRoot : ∀ i : Fin q.closureRule.rootSize,
      t (i.castLE q.closureRule.rootLE) ∈ H := by
    intro i
    have hMem : root i ∈ H :=
      subset_UClosureHull L.patternClosureRules C (Set.range root)
        ⟨i, rfl⟩
    have hIdx :
        i.castLE q.closureRule.rootLE = Fin.castSucc i := by
      apply Fin.ext
      rfl
    have hEq :
        t (i.castLE q.closureRule.rootLE) = t (Fin.castSucc i) :=
      congrArg t hIdx
    exact Eq.mp (congrArg (fun a => a ∈ H) hEq.symm) hMem
  exact (UClosureHull_isUSubstructure L.patternClosureRules C
    (Set.range root))
      q.closureRule ⟨q, rfl⟩ t hTag hRoot
      (Fin.last p.rootSize)

end StructuralRamsey.RelStructure

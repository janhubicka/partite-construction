import PartiteConstruction.Functional.PatternTagIdentity2019
import PartiteConstruction.Functional.PatternCompleteRootExtraction2019

/-!
# Uniqueness of an OLD function output over one complete active root

Normality turns every OLD graph tuple into a genuine FRESH tagged
closure tuple over its *complete* full old root pattern.
The original 2019 U-closedness condition then forces the tagged
closure tuple to be UNIQUE over each embedding of the root.

Thus the OLD graph has at most one output for each fixed input
equality-pattern and exact injective root enumeration.
No global canonicality, B-cover, order, or source-hull size bound is
needed for this local uniqueness lemma. Comparing DIFFERENT root
patterns for the same primitive input remains a separate step.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Two old output tuples over a fixed active full function root
coincide. This is the U-closed *fresh tag* uniqueness mechanism
of the 2019 partial-function representation. -/
theorem PatternTagNormal.same_root_output_unique
    (C : RelStructure (L.patternTag) V)
    (hC : IsUClosed L.patternClosureRules C)
    (hNormal : PatternTagNormal C)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (hDom : (patternTagReduct C).rel (.inr (.inl p)) root)
    (y z : V)
    (hy : (patternTagReduct C).rel (.inr (.inr p))
      (Structure.funcTuple root y))
    (hz : (patternTagReduct C).rel (.inr (.inr p))
      (Structure.funcTuple root z)) :
    y = z := by
  classical
  let E := patternTagReduct C
  let q : Language.FunctionRootPattern L :=
    Language.FunctionRootPattern.ofActiveDomain E
      p hpos root hDom
  let rootOld : Embedding q.root E :=
    Language.FunctionRootPattern.ofActiveDomain_embedding
      E p hpos root hinj hDom
  let rootTag : Embedding (q.closureRule.root)
      (patternTagExpansion E) := rootOld.patternTag
  let tagged : Embedding (patternTagExpansion E) C :=
    hNormal.canonicalEmbedding
  let eRoot : Embedding q.closureRule.root C :=
    tagged.comp rootTag
  have hRelY :
      C.rel (.inr q) (Structure.funcTuple root y) := by
    apply (hNormal q (Structure.funcTuple root y)).2
    exact patternTagExpansion_tag_of_valid_old_output
      E p hpos (Structure.funcTuple root y) hy hinj hDom
  have hRelZ :
      C.rel (.inr q) (Structure.funcTuple root z) := by
    apply (hNormal q (Structure.funcTuple root z)).2
    exact patternTagExpansion_tag_of_valid_old_output
      E p hpos (Structure.funcTuple root z) hz hinj hDom
  have heRoot (i : Fin p.rootSize) : eRoot i = root i := by
    rfl
  have hPreY : ∀ i : Fin q.closureRule.rootSize,
      (Structure.funcTuple root y)
        (i.castLE q.closureRule.rootLE) = eRoot i := by
    intro i
    change (Structure.funcTuple root y) i.castSucc = eRoot i
    rw [Structure.funcTuple_castSucc, heRoot]
  have hPreZ : ∀ i : Fin q.closureRule.rootSize,
      (Structure.funcTuple root z)
        (i.castLE q.closureRule.rootLE) = eRoot i := by
    intro i
    change (Structure.funcTuple root z) i.castSucc = eRoot i
    rw [Structure.funcTuple_castSucc, heRoot]
  obtain ⟨t, ht, htunique⟩ :=
    (hC q.closureRule ⟨q, rfl⟩).2 eRoot
  have hyT : Structure.funcTuple root y = t :=
    htunique (Structure.funcTuple root y) ⟨hRelY, hPreY⟩
  have hzT : Structure.funcTuple root z = t :=
    htunique (Structure.funcTuple root z) ⟨hRelZ, hPreZ⟩
  have hLast := congrArg
    (fun f : Fin (p.rootSize + 1) → V => f (Fin.last p.rootSize))
    (hyT.trans hzT.symm)
  simpa only [Structure.funcTuple_last] using hLast

end StructuralRamsey.RelStructure

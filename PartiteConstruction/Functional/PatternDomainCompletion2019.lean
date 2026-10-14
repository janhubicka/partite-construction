import PartiteConstruction.Functional.PatternSameRootUniqueness2019

/-!
# Active OLD partial-function domains have their closure output

In a U-closed, tag-normal Picture, every embedded complete positive
OLD function-root pattern has exactly one fresh closure tuple.
The OLD graph part of that tagged tuple is therefore a genuine output
of the primitive partial function on precisely those source inputs.

This proves existence (domain -> nonempty graph), complementing the
already verified graph -> domain validity and fixed-root uniqueness.
It does not assume that an arbitrary noncanonical Picture is globally
a canonical expansion, nor introduce additional root vertices.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every valid OLD domain relation with a distinct, positive root
has a true OLD output graph tuple over precisely that root. -/
theorem PatternTagNormal.old_domain_has_output_tuple
    (C : RelStructure (L.patternTag) V)
    (hC : IsUClosed L.patternClosureRules C)
    (hNormal : PatternTagNormal C)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (hDom : (patternTagReduct C).rel (.inr (.inl p)) root) :
    ∃ t : Fin (p.rootSize + 1) → V,
      (patternTagReduct C).rel (.inr (.inr p)) t ∧
      (∀ i : Fin p.rootSize, t i.castSucc = root i) := by
  classical
  let E := patternTagReduct C
  let q : Language.FunctionRootPattern L :=
    Language.FunctionRootPattern.ofActiveDomain E
      p hpos root hDom
  let rootOld : Embedding q.root E :=
    Language.FunctionRootPattern.ofActiveDomain_embedding
      E p hpos root hinj hDom
  let rootTag : Embedding q.closureRule.root (patternTagExpansion E) :=
    rootOld.patternTag
  let tagged : Embedding (patternTagExpansion E) C :=
    hNormal.canonicalEmbedding
  let eRoot : Embedding q.closureRule.root C :=
    tagged.comp rootTag
  have heRoot (i : Fin p.rootSize) : eRoot i = root i := by
    rfl
  obtain ⟨t, ht, _⟩ := (hC q.closureRule ⟨q, rfl⟩).2 eRoot
  have hOld : E.rel (.inr (.inr p)) t :=
    ((hNormal q t).mp ht.1).1
  refine ⟨t, hOld, ?_⟩
  intro i
  have hIdx :
      i.castLE q.closureRule.rootLE = Fin.castSucc i := by
    apply Fin.ext
    rfl
  exact (congrArg t hIdx).symm.trans ((ht.2 i).trans (heRoot i))

/-- The active OLD domain of a positive equality pattern produces an
actual primitive OLD graph value, not just an abstract fresh tag. -/
theorem PatternTagNormal.old_domain_has_output
    (C : RelStructure (L.patternTag) V)
    (hC : IsUClosed L.patternClosureRules C)
    (hNormal : PatternTagNormal C)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (hDom : (patternTagReduct C).rel (.inr (.inl p)) root) :
    ∃ y : V,
      (patternTagReduct C).rel (.inr (.inr p))
        (Structure.funcTuple root y) := by
  obtain ⟨t, hGraph, hPrefix⟩ :=
    hNormal.old_domain_has_output_tuple C hC p hpos root hinj hDom
  let y := t (Fin.last p.rootSize)
  have hTuple : t = Structure.funcTuple root y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [y, Structure.funcTuple_last]
    · simpa only [Structure.funcTuple_castSucc] using hPrefix i
  refine ⟨y, ?_⟩
  rw [← hTuple]
  exact hGraph

end StructuralRamsey.RelStructure

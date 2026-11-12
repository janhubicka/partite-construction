import PartiteConstruction.Functional.EHNDefectCrossingGenerators

/-!
# Track D: a relation or function EHN reflection defect needs two distinct inputs

The verified source-crossing generator certificate can be sharpened:
in a proper FULL free decomposition of the function-closed hull generated
by original inputs xs, there must be TWO DISTINCT source input VERTICES.
Indeed one original generator cannot simultaneously be missing from both
full closed sides, since the free amalgam covers the whole generated hull.

Consequently every target-only OLD relation tuple and every source-undefined
but target-defined OLD function tuple has at least two distinct original
input vertices. This is stronger than just having two indices: repeated
inputs do not count. Nullary and unary input defects are impossible.

If the whole language has relation and function arities at most one,
an EHN map that is injective on VERTICES is therefore automatically a FULL
native embedding on the very same vertex map. This has no source-finiteness
hypothesis and does not infer any generator-rank drop for decomposition
SIDES in a higher-arity mixed HJ test.

Not the missing common-root relative strict B-tree construction.
Numbered survey Appendix A stays frozen.
-/

namespace StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {U V : Type v} {I : Type w}

/-- A proper free decomposition of a FULL input-generated hull requires
at least TWO DISTINCT ORIGINAL INPUT VERTICES. This uses the actual
free-amalgam cover, not an inference about generated ranks of its sides. -/
theorem ProperFreeDecomposition.crossedInputGenerators_distinct_vertices
    (C : Structure L U) (xs : I → U)
    (d : ProperFreeDecomposition
      (C.induce (C.functionClosure (Set.range xs))
        (C.functionClosure_isClosed (Set.range xs)))) :
    ∃ i j : I, xs i ≠ xs j := by
  classical
  obtain ⟨⟨i, hLeft⟩, ⟨j, hRight⟩⟩ :=
    d.crossedInputGenerators C xs
  let H : Set U := C.functionClosure (Set.range xs)
  let q : I → H := fun k =>
    ⟨xs k, C.subset_functionClosure (Set.range xs) ⟨k, rfl⟩⟩
  change q i ∉ Set.range d.leftIn at hLeft
  change q j ∉ Set.range d.rightIn at hRight
  refine ⟨i, j, ?_⟩
  intro hSame
  have hq : q i = q j := Subtype.ext hSame
  rcases d.free.covers (q i) with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact hLeft ⟨a, ha.symm⟩
  · exact hRight ⟨b, (hq.symm.trans hb).symm⟩

/-- A target-only positive relation on the image of an ACTUAL original
tuple can occur only if that tuple contains two distinct source vertices.
Nullary/unary relation reflection failures are impossible under EHN. -/
theorem IsEHNHomomorphismEmbedding.relationFailure_hasTwoDistinctInputs
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (R : L.RelSymbol) (xs : Fin (L.relArity R) → U)
    (hTarget : D.rel R (p ∘ xs))
    (hSource : ¬ C.rel R xs) :
    ∃ i j : Fin (L.relArity R), xs i ≠ xs j := by
  obtain ⟨d⟩ :=
    hp.relationInputHull_reducible_of_reflectionFailure
      R xs hTarget hSource
  exact d.crossedInputGenerators_distinct_vertices C xs

/-- The same sharp two-distinct-source-input bound holds for a
target-defined/source-undefined function application. It does not
concern extra outputs on a SOURCE-DEFINED application, which EHN
fibre exactness already rules out. -/
theorem IsEHNHomomorphismEmbedding.domainFailure_hasTwoDistinctInputs
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
    (hTarget : (D.func F (p ∘ xs)).Nonempty)
    (hSource : ¬ (C.func F xs).Nonempty) :
    ∃ i j : Fin (L.funcArity F), xs i ≠ xs j := by
  obtain ⟨d⟩ :=
    hp.inputHull_reducible_of_domainFailure F xs hTarget hSource
  exact d.crossedInputGenerators_distinct_vertices C xs

/-- In a language of arity AT MOST ONE for both old relations and
old functions, the only possible failure of FULL EHN embedding is a
vertex-label collision. Thus globally vertex-injective EHN projections
are FULL embeddings on the same map, even for infinite source carriers
and in the presence of nullary symbols. -/
theorem IsEHNHomomorphismEmbedding.fullEmbedding_of_allArity_le_one
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hInjective : Function.Injective p)
    (hRelArity : ∀ R, L.relArity R ≤ 1)
    (hFuncArity : ∀ F, L.funcArity F ≤ 1) :
    ∃ e : Embedding C D, ∀ x : U, e x = p x := by
  classical
  by_contra hNoFull
  rcases hp.nonFull_exactThreeDefects hNoFull with
      ⟨x, y, hDistinct, hEq⟩ |
      ⟨R, xs, hTarget, hSource⟩ |
      ⟨F, xs, hTarget, hSource⟩
  · exact hDistinct (hInjective hEq)
  · obtain ⟨i, j, hij⟩ :=
      hp.relationFailure_hasTwoDistinctInputs R xs hTarget hSource
    have hIJ : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      have hn := hRelArity R
      omega
    exact hij (congrArg xs hIJ)
  · obtain ⟨i, j, hij⟩ :=
      hp.domainFailure_hasTwoDistinctInputs F xs hTarget hSource
    have hIJ : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      have hn := hFuncArity F
      omega
    exact hij (congrArg xs hIJ)

end StructuralRamsey.Structure

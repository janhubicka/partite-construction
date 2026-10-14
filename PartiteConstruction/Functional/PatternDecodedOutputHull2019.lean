import PartiteConstruction.Functional.PatternOutputClosure2019
import PartiteConstruction.Functional.PartialFunctionPatternDecode2019

/-!
# Every decoded positive-arity output lies in the EXACT input hull

An arbitrary equality-pattern witness to membership in the decoded
function fibre comes with a surjective map from original argument
positions to distinct root vertices. Its root range is therefore
EXACTLY the set of original argument vertices, even for repeated inputs.

For a positive-arity symbol the distinct root is nonempty, and
tag-normality makes each valid OLD graph tuple a fresh closure
tuple. The output must then lie in the U-closure of the original
argument-vertex set, independently of the equality-pattern encoding.

This is the key input to the common-protected-hull proof of
cross-pattern output uniqueness. It does not enlarge an exact weak
source test to its closure; the hull is used only as the target of
a separate protected completion argument.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Any two surjective factorisations through distinct input roots
have exactly the same range as the original argument tuple. -/
theorem equalityPattern_range_eq
    {a m : ℕ} (x : Fin a → V)
    (r : Fin a → Fin m) (hr : Function.Surjective r)
    (root : Fin m → V)
    (hFact : ∀ i, x i = root (r i)) :
    Set.range root = Set.range x := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hr i
    refine ⟨j, ?_⟩
    calc
      x j = root (r j) := hFact j
      _ = root i := congrArg root hj
  · rintro ⟨j, rfl⟩
    exact ⟨r j, (hFact j).symm⟩

/-- Every output of the *decoded* OLD positive-arity function fibre
lies in the U-hull of the exact original input vertices, regardless
of which equality-pattern root witnessed that output. -/
theorem PatternTagNormal.decoded_output_mem_inputHull
    (C : RelStructure (L.patternTag) V)
    (hNormal : PatternTagNormal C)
    (F : L.FuncSymbol) (hArity : 0 < L.funcArity F)
    (x : Fin (L.funcArity F) → V) (y : V)
    (hy : y ∈ (Structure.patternDecode
      (patternTagReduct C)).func F x) :
    y ∈ UClosureHull L.patternClosureRules C (Set.range x) := by
  obtain ⟨m, r, hr, root, hInj, hFact, hDom, hGraph⟩ := hy
  have hmPos : 0 < m := by
    by_contra h
    have hmZero : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact Fin.elim0 (r ⟨0, hArity⟩)
  let p : Language.FunctionInputPattern L := {
    symbol := F
    rootSize := m
    argMap := r
    onto := hr
  }
  have hPrefixInj : Function.Injective
      (fun i : Fin m => (Structure.funcTuple root y) i.castSucc) := by
    simpa only [Structure.funcTuple_castSucc] using hInj
  have hPrefixDom : (patternTagReduct C).rel (.inr (.inl p))
      (fun i : Fin m => (Structure.funcTuple root y) i.castSucc) := by
    simpa only [Structure.funcTuple_castSucc] using hDom
  have hOutput : y ∈
      UClosureHull L.patternClosureRules C (Set.range root) := by
    have h := hNormal.old_output_mem_generatedHull
      C p hmPos (Structure.funcTuple root y)
      hGraph hPrefixInj hPrefixDom
    simpa only [Structure.funcTuple_last,
      Structure.funcTuple_castSucc] using h
  rw [equalityPattern_range_eq x r hr root hFact] at hOutput
  exact hOutput

end StructuralRamsey.RelStructure

import PartiteConstruction.Ramsey.ClosureWeakRestrictionPower

/-! # Relative closure of native Hales--Jewett line copies

Partial uniqueness of the base suffices to prove that EVERY native line
copy is a relative U-substructure of its coordinate power. At a variable
coordinate compare with one fixed variable coordinate; at a constant
coordinate compare with the letter image of the projected closure tuple.
No total closure, closed control, or vertex coverage by A-copies is used.
The finite Ramsey statement selects these very lines, not arbitrary
embeddings for which relative closedness has not been established.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree
universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v} {N : ℕ}

/-- Each native line range is relatively closed even when the base is
only semi-closed. The part structure itself need not be closed. -/
theorem line_range_isUSubstructure_of_semiClosed
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V) (hPart : B.IsPartiteOver A)
    (hB : IsUSemiClosed rules B.toRelStructure)
    (line : Line (Letter A B) N) :
    IsUSubstructure rules (power B N).toRelStructure
      (Set.range (lineEmbedding hPart line).toEmbedding) := by
  classical
  obtain ⟨k0, hk0⟩ := line.hasParameter
  intro rule hrule t ht hRoot j
  let xs : Fin rule.rootSize → V := fun i => Classical.choose (hRoot i)
  have hxs (i : Fin rule.rootSize) :
      NonInduced.lineMap line (xs i) = t (i.castLE rule.rootLE) :=
    Classical.choose_spec (hRoot i)
  let y : Fin (L.arity rule.symbol) → V := fun l => (t l).coord k0
  have hyRoot (i : Fin rule.rootSize) : y (i.castLE rule.rootLE) = xs i := by
    have h := congrArg (fun z : Vertex B N => z.coord k0) (hxs i)
    simpa only [NonInduced.lineMap, hk0] using h.symm
  have hy : B.rel rule.symbol y := ht k0
  have hProjected : A.rel rule.symbol (B.part ∘ y) := hPart.1 rule.symbol y hy
  refine ⟨y j, ?_⟩
  apply NonInduced.Vertex.ext B
  · exact (t j).belongs k0
  · intro k
    cases hk : line.symbol k with
    | parameter =>
        have hEq : (fun l => (t l).coord k) = y := by
          apply (hB rule hrule).2 _ _ (ht k) hy
          intro i
          have h := congrArg (fun z : Vertex B N => z.coord k) (hxs i)
          have hRootK : (t (i.castLE rule.rootLE)).coord k = xs i := by
            simpa only [NonInduced.lineMap, hk] using h.symm
          exact hRootK.trans (hyRoot i).symm
        change (NonInduced.lineMap line (y j)).coord k = (t j).coord k
        simpa only [NonInduced.lineMap, hk] using (congrFun hEq j).symm
    | const a =>
        have hLetter : B.rel rule.symbol (a ∘ (B.part ∘ y)) :=
          (a.toEmbedding.map_rel_iff rule.symbol (B.part ∘ y)).mpr hProjected
        have hEq : (fun l => (t l).coord k) = a ∘ (B.part ∘ y) := by
          apply (hB rule hrule).2 _ _ (ht k) hLetter
          intro i
          have h := congrArg (fun z : Vertex B N => z.coord k) (hxs i)
          have hRootK : (t (i.castLE rule.rootLE)).coord k = a (B.part (xs i)) := by
            simpa only [NonInduced.lineMap, hk] using h.symm
          exact hRootK.trans (congrArg (fun x => a (B.part x)) (hyRoot i).symm)
        change (NonInduced.lineMap line (y j)).coord k = (t j).coord k
        simpa only [NonInduced.lineMap, hk, Function.comp_apply] using (congrFun hEq j).symm

/-- The finite partite lemma with the EXACT line family retained.
It gives a semi-closed native power and relatively closed line copies. -/
theorem semiClosed_partiteLemma_lines
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V) (hPart : B.IsPartiteOver A)
    (hB : IsUSemiClosed rules B.toRelStructure)
    [Finite P] [Finite V] (Color : Type*) [Fintype Color] :
    ∃ N : ℕ, 0 < N ∧
      IsUSemiClosed rules (power B N).toRelStructure ∧
      (∀ line : Line (Letter A B) N,
        IsUSubstructure rules (power B N).toRelStructure
          (Set.range (lineEmbedding hPart line).toEmbedding)) ∧
      (∀ chi : Partite.Embedding (transversal A) (power B N) → Color,
        ∃ line : Line (Letter A B) N,
          ∀ a b : Letter A B,
            chi ((lineEmbedding hPart line).comp a) =
            chi ((lineEmbedding hPart line).comp b)) := by
  classical
  letI : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := Color)
  refine ⟨N, hN, power_isUSemiClosed B hB hN,
    fun line => line_range_isUSubstructure_of_semiClosed B hPart hB line, ?_⟩
  intro chi
  obtain ⟨line, hline⟩ := hHJ (fun w => chi (wordEmbedding hPart hN w))
  refine ⟨line, ?_⟩
  intro a b
  simpa only [lineEmbedding_comp_letter hPart hN] using hline a b

end StructuralRamsey.Partite.Induced

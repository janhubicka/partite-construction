import PartiteConstruction.Ramsey.ClosureUIrreducible2019

/-! # A regression test for intrinsic versus relative U-irreducibility

The current `IsUIrreducible` tests indecomposability into *intrinsically*
U-closed sides.  This is a much stronger condition on a non-U-closed
structure than indecomposability into relative U-substructures.

If an embedded closure root has no closure relation tuple at all, the
structure cannot be a free amalgam of intrinsically U-closed sides.
Consequently, it is `IsUIrreducible` in this literal sense, even if
it is graph-reducible.  For a weak induced substructure of a U-closed
ambient structure such missing outputs occur naturally when outputs
are outside the tested vertex set.

This is a deliberately limited *positive theorem* about our current
definition, NOT a claim that the published 2019 definition uses that
interpretation.  It motivates the parallel relative notion.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U : Type v}

/-- A missing tuple over a valid root makes the structure
indecomposable into intrinsically U-closed free-amalgam sides.
In particular the theorem has no premise that A itself is U-closed. -/
theorem IsUIrreducible.of_missing_closureTuple
    {rules : ClosureDescription L}
    {A : RelStructure L U}
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root A)
    (hMissing :
      ¬ ∃ t : Fin (L.arity rule.symbol) → U,
          A.rel rule.symbol t ∧
          ∀ k : Fin rule.rootSize,
            t (k.castLE rule.rootLE) = e k) :
    IsUIrreducible rules A := by
  classical
  intro H E F Root Left Right sL sR iL iR hLeft hRight hFree
  exfalso
  have hRootIrred :
      (A.induce (Set.range e)).Irreducible :=
    rule.rootIrreducible.range_embedding e
  rcases hFree.irreducible_side (Set.range e) hRootIrred with
      hInLeft | hInRight
  · have hRange : ∀ k : Fin rule.rootSize,
        ∃ a : E, e k = iL a := by
      intro k
      exact hInLeft ⟨e k, ⟨k, rfl⟩⟩
    let eL : Embedding rule.root Left :=
      e.factorThroughRangeHeterogeneous iL hRange
    obtain ⟨t, ht, _⟩ := (hLeft rule hrule).2 eL
    apply hMissing
    refine ⟨iL ∘ t, ?_, ?_⟩
    · exact (iL.map_rel_iff rule.symbol t).mpr ht.1
    · intro k
      change iL (t (k.castLE rule.rootLE)) = e k
      rw [ht.2 k]
      exact (Classical.choose_spec (hRange k)).symm
  · have hRange : ∀ k : Fin rule.rootSize,
        ∃ b : F, e k = iR b := by
      intro k
      exact hInRight ⟨e k, ⟨k, rfl⟩⟩
    let eR : Embedding rule.root Right :=
      e.factorThroughRangeHeterogeneous iR hRange
    obtain ⟨t, ht, _⟩ := (hRight rule hrule).2 eR
    apply hMissing
    refine ⟨iR ∘ t, ?_, ?_⟩
    · exact (iR.map_rel_iff rule.symbol t).mpr ht.1
    · intro k
      change iR (t (k.castLE rule.rootLE)) = e k
      rw [ht.2 k]
      exact (Classical.choose_spec (hRange k)).symm

end StructuralRamsey.RelStructure

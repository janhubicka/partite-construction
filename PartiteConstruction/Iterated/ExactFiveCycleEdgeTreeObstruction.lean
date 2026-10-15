import PartiteConstruction.Iterated.OddCycleEdgeTreeObstruction

/-!
# The exact five-cycle of the maximal mixed hard-root audit

The arbitrary-stage hard-root counterexample uses the five-vertex
closed test with projected part sequence 0-1-3-2-4-0. Up to relabelling,
that test is simply the genuine graph five-cycle C5. The earlier
odd-cycle Lean obstruction was expressed as a loose amalgam of two
four-vertex paths; here we add a direct **five-vertex carrier**
presentation, making the pending native EHN-test identification
a literal finite relation-table check.

This file certifies that the concrete five-vertex graph admits NO
relational homomorphism-embedding into any strict tree of K2 edges.
The source graph is finite and the proof uses the already verified
two-colourability invariant for strict K2 trees. The additional claim
that this graph is an exact closed native function-language attachment
test remains a separate, explicitly unverified Lean obligation.
-/

namespace StructuralRamsey.RelStructure.LooseNotStrictifiable

/-- Undirected five-cycle, in the existing binary relation language.
Its vertices are indexed 0,1,2,3,4 along the cyclic walk. -/
def FiveCycle : RelStructure L (Fin 5) where
  rel := fun _ x =>
    (x i0).val + 1 = (x i1).val ∨
    (x i1).val + 1 = (x i0).val ∨
    (x i0 = 0 ∧ x i1 = 4) ∨
    (x i0 = 4 ∧ x i1 = 0)

/-- The explicitly labelled five-cycle is not two-colourable. -/
theorem FiveCycle_not_twoColorable : ¬ TwoColorable FiveCycle := by
  rintro ⟨c, hc⟩
  have edgeCol (a b : Fin 5)
      (h : FiveCycle.rel ()
        (fun k => if k = i0 then a else b)) :
      c a ≠ c b := by
    have h := hc _ h
    simpa [i0_ne_i1.symm] using h
  have h01 : c (0 : Fin 5) ≠ c 1 := edgeCol 0 1 (by simp [FiveCycle, i0, i1])
  have h12 : c (1 : Fin 5) ≠ c 2 := edgeCol 1 2 (by simp [FiveCycle, i0, i1])
  have h23 : c (2 : Fin 5) ≠ c 3 := edgeCol 2 3 (by simp [FiveCycle, i0, i1])
  have h34 : c (3 : Fin 5) ≠ c 4 := edgeCol 3 4 (by simp [FiveCycle, i0, i1])
  have h40 : c (4 : Fin 5) ≠ c 0 := edgeCol 4 0 (by simp [FiveCycle, i0, i1])
  have h02 : c (0 : Fin 5) = c 2 := bool_eq_of_ne_ne h01 h12
  have h24 : c (2 : Fin 5) = c 4 := bool_eq_of_ne_ne h23 h34
  exact h40 (h02.trans h24).symm

/-- No map preserving the edges of the exact five-vertex test can
land in any strict K2-tree, even if one is free to choose an arbitrary
root map or completed target tree.

This checks the **intrinsic target obstruction**, not yet the whole
stage-level hypothesis of the overly universal sparsening schema. -/
theorem FiveCycle_not_strict_edge_tree :
    ¬ ∃ (W : Type) (T : RelStructure L W),
      TreeAmalgam Edge W T ∧
      ∃ f : Fin 5 → W,
        FiveCycle.IsHomomorphismEmbedding T f := by
  rintro ⟨W, T, hTree, f, hf⟩
  have hCol : TwoColorable T :=
    TreeAmalgam.twoColorable Edge_twoColorable hTree
  exact FiveCycle_not_twoColorable (hCol.pullback f hf.1)

end StructuralRamsey.RelStructure.LooseNotStrictifiable

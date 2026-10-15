import PartiteConstruction.Iterated.LooseStrictificationObstruction

/-!
# Lean-certified odd-cycle obstruction to any strict edge-tree completion

The previous loose-P4 counterexample contains a five-cycle, and its
non-two-colourability was already certified.  For the actual maximal
mixed-root functional sparsening audit the relevant base is instead
the irreducible two-vertex EDGE (K₂): both of the graph paths that
form the five-cycle are genuine strict K₂-trees.

Here we reuse the checked two-colourability invariant and the
existing explicit odd free amalgam to prove that this concrete
amalgam has NO homomorphism-embedding into ANY strict K₂-tree.
This is an unconditional Lean theorem.  It isolates the graph
obstruction used by the separate finite native-EHN stage audit.

It does NOT yet certify that the entire stage-level
`MaximalMixedHardRootSchemaFromTwo` has a counterexample: doing so
additionally requires formalizing the two partite stages, their
distinct five-part projection and their exact closed test. The
stage-level construction is documented separately and is not
presented here as a proved Lean theorem.
-/

namespace StructuralRamsey.RelStructure.LooseNotStrictifiable

/-- The irreducible graph edge, with a symmetric irreflexive binary
relation. It is the graph analogue of the Base=K₂ used in the native
hard-root audit, not the reducible P4 base of the previous theorem. -/
def Edge : RelStructure L (Fin 2) where
  rel := fun _ x => x i0 ≠ x i1

/-- The edge has a proper two-colouring. -/
theorem Edge_twoColorable : TwoColorable Edge := by
  let c : Fin 2 → Bool := fun x => x == 0
  have hc : Function.Injective c := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [c]
  refine ⟨c, ?_⟩
  intro x hx
  intro hcol
  exact hx (hc hcol)

/-- The SAME explicit five-cycle-bearing loose free amalgam cannot
admit an original relational homomorphism-embedding into a strict
K₂-tree. This obstruction is independent of rooting or part labels:
it holds even when the target map is completely unconstrained. -/
theorem OddLoose_not_strict_edge_tree :
    ¬ ∃ (W : Type) (T : RelStructure L W),
      TreeAmalgam Edge W T ∧
      ∃ f : FreeAmalgam.Vertex Root P4 P4 leftRoot rightRoot → W,
        OddLoose.IsHomomorphismEmbedding T f := by
  rintro ⟨W, T, hTree, f, hf⟩
  have hCol : TwoColorable T :=
    TreeAmalgam.twoColorable Edge_twoColorable hTree
  exact OddLoose_not_twoColorable (hCol.pullback f hf.1)

end StructuralRamsey.RelStructure.LooseNotStrictifiable

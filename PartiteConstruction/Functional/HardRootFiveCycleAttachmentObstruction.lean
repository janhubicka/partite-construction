import PartiteConstruction.Functional.HardRootFiveCycleFixture
import PartiteConstruction.Iterated.ExactFiveCycleEdgeTreeObstruction

/-!
# An actual selected-support free attachment contains an odd cycle

The exact old and core finite forests in HardRootFiveCycleFixture
form a genuine FULL relational free attachment along the entire
selected support. Its cyclic edges are:

  core c0--d1--c3 = old a3--b2--b4--a0 = core c0.

We certify these five edges in the actual free-amalgam carrier, not
just in a separate abstract graph. Thus even this attached structure
cannot map by a relational homomorphism into a strict tree of K2
copies. This rules out the UNIVERSAL arbitrary-stage hard-root
relative-extension schema.

This is NOT yet a certification of the native EHN Stage object or
the exact five-vertex closed maximal-image generator test. Nor is
this core a genuine Hales--Jewett power of the selected support:
it contains a vertex with part 1 outside selected parts {0,3}.
Consequently the proof does NOT refute history-restricted actual
HJ Picture completion.
-/

namespace StructuralRamsey.RelStructure.LooseNotStrictifiable.HardRootC5

open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.LooseNotStrictifiable

noncomputable section

/-- A binary edge in the actual relational free attachment. -/
def joinedEdge
    (a b : FreeAmalgam.Vertex oldSelected coreGraph oldGraph
      selectedEmbedding (inclusion oldGraph selected)) : Prop :=
  joined.rel () (fun k => if k = i0 then a else b)

/-- Every CORE edge survives in the actual amalgam on the same two
vertices, by the verified full core embedding. -/
theorem joinedEdge_core (a b : Fin 5) (h : coreAdjacent a b) :
    joinedEdge (coreInto a) (coreInto b) := by
  let tup : Fin (L.arity ()) → Fin 5 :=
    fun k => if k = i0 then a else b
  have hcore : coreGraph.rel () tup := by
    change coreAdjacent (tup i0) (tup i1)
    simpa only [tup, if_pos rfl, if_neg i0_ne_i1.symm] using h
  have hmap : joined.rel () (coreInto ∘ tup) :=
    (coreInto.map_rel_iff () tup).mpr hcore
  have heq : (coreInto ∘ tup) =
      (fun k : Fin (L.arity ()) =>
        if k = i0 then coreInto a else coreInto b) := by
    funext k
    by_cases hk : k = i0 <;> simp [tup, hk]
  rw [heq] at hmap
  exact hmap

/-- Every OLD edge survives in the actual attached copy. -/
theorem joinedEdge_old (a b : Fin 6) (h : oldAdjacent a b) :
    joinedEdge (oldInto a) (oldInto b) := by
  let tup : Fin (L.arity ()) → Fin 6 :=
    fun k => if k = i0 then a else b
  have hold : oldGraph.rel () tup := by
    change oldAdjacent (tup i0) (tup i1)
    simpa only [tup, if_pos rfl, if_neg i0_ne_i1.symm] using h
  have hmap : joined.rel () (oldInto ∘ tup) :=
    (oldInto.map_rel_iff () tup).mpr hold
  have heq : (oldInto ∘ tup) =
      (fun k : Fin (L.arity ()) =>
        if k = i0 then oldInto a else oldInto b) := by
    funext k
    by_cases hk : k = i0 <;> simp [tup, hk]
  rw [heq] at hmap
  exact hmap

/-- The ACTUAL old/core attachment is not two-colourable.
Its five successive vertices are c0,d1,c3,b2,b4. The two
support identifications close a five-cycle without asserting
that every other vertex belongs to the cycle. -/
theorem joined_not_twoColorable : ¬ TwoColorable joined := by
  rintro ⟨c, hc⟩
  have edgeColor (a b : FreeAmalgam.Vertex oldSelected coreGraph oldGraph
      selectedEmbedding (inclusion oldGraph selected))
      (h : joinedEdge a b) : c a ≠ c b := by
    have he := hc (fun k => if k = i0 then a else b) h
    simpa [i0_ne_i1.symm] using he
  have h01 : c (coreInto 0) ≠ c (coreInto 1) :=
    edgeColor _ _ (joinedEdge_core 0 1 (by simp [coreAdjacent, coreEdges]))
  have h12 : c (coreInto 1) ≠ c (coreInto 2) :=
    edgeColor _ _ (joinedEdge_core 1 2 (by simp [coreAdjacent, coreEdges]))
  have h23 : c (coreInto 2) ≠ c (oldInto 2) := by
    rw [overlap_at_a3]
    exact edgeColor _ _ (joinedEdge_old 3 2
      (by simp [oldAdjacent, oldEdges]))
  have h34 : c (oldInto 2) ≠ c (oldInto 1) :=
    edgeColor _ _ (joinedEdge_old 2 1 (by simp [oldAdjacent, oldEdges]))
  have h40 : c (oldInto 1) ≠ c (coreInto 0) := by
    rw [overlap_at_a0]
    exact edgeColor _ _ (joinedEdge_old 1 0
      (by simp [oldAdjacent, oldEdges]))
  have h02 : c (coreInto 0) = c (coreInto 2) :=
    bool_eq_of_ne_ne h01 h12
  have h24 : c (coreInto 2) = c (oldInto 1) :=
    bool_eq_of_ne_ne h23 h34
  exact h40 (h02.trans h24).symm

/-- No relational homomorphism-embedding of the ACTUAL selected-support
free attachment can land in any strict tree of K2 edge copies.
The obstruction is independent of any chosen target root map. -/
theorem joined_not_strict_edge_tree :
    ¬ ∃ (W : Type) (T : RelStructure L W),
      TreeAmalgam Edge W T ∧
      ∃ f : FreeAmalgam.Vertex oldSelected coreGraph oldGraph
          selectedEmbedding (inclusion oldGraph selected) → W,
        joined.IsHomomorphismEmbedding T f := by
  rintro ⟨W,T,hTree,f,hf⟩
  have hCol : TwoColorable T :=
    TreeAmalgam.twoColorable Edge_twoColorable hTree
  exact joined_not_twoColorable (hCol.pullback f hf.1)

end

end StructuralRamsey.RelStructure.LooseNotStrictifiable.HardRootC5

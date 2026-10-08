import PartiteConstruction.Functional.PublishedTotalBinaryObstruction
import PartiteConstruction.Iterated.LocalTreeLike

/-! # The counterexample has trivial closures and hereditary graph irreducibility

For F(x,y)={x}, every vertex subset is closed. Weakly induced images and
full induced images of the input algebras therefore coincide. Moreover,
every induced function-graph subset is irreducible. Thus neither closure
bookkeeping nor adding hereditary irreducibility hypotheses repairs the
literal full-projection sparsening statement.
-/

namespace StructuralRamsey.Structure.PublishedTotalBinaryObstruction

/-- These algebras have no nontrivial function closure. -/
theorem algebra_all_sets_closed (V : Type) (S : Set V) :
    (algebra V).IsClosed S := by
  intro F x hx y hy
  change y = x (0 : Fin 2) at hy
  rw [hy]
  exact hx (0 : Fin 2)

/-- The function incidence (x,y,x) witnesses every pair inside every
induced graph subset. -/
theorem algebra_graph_hereditarilyIrreducible (V : Type) :
    (algebra V).graph.HereditarilyIrreducible := by
  intro S x y hne
  refine ⟨(.inr () : language.graph.Symbol), ![x, y, x],
    (0 : Fin 3), (1 : Fin 3), ?_, rfl, rfl⟩
  change x.1 = x.1
  rfl

/-- Even hereditary irreducibility of both input function graphs does not
repair the full-functional statement. -/
theorem counterexample_even_hereditary_graphs :
    A.graph.HereditarilyIrreducible ∧ B.graph.HereditarilyIrreducible ∧
    D.graph.HereditarilyIrreducible ∧
    (∀ n : ℕ, ¬ PublishedSparseningConclusion A B D (Fin 2) n) := by
  exact ⟨algebra_graph_hereditarilyIrreducible _,
    algebra_graph_hereditarilyIrreducible _,
    algebra_graph_hereditarilyIrreducible _,
    not_publishedSparseningConclusion_all⟩

end StructuralRamsey.Structure.PublishedTotalBinaryObstruction

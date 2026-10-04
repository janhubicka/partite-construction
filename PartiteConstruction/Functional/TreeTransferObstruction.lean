import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Functional.SingletonExpansion
import PartiteConstruction.Structure.Relationalize

/-! # Functional obstruction to naive relational tree transfer

Replacing a partial function by its graph relation is exact on weak
substructures, but an arbitrary relational tree amalgam need not decode to a
functional tree amalgam.  The obstruction already occurs for one unary
partial function: glue two copies of a two-point partial-function structure
over the input vertex while omitting its output from the root.  The relational
free amalgam then has two distinct outputs over the common input.

This regression test records why the relational sparsening theorem cannot be
transferred to function languages merely by graph encoding.  A successful
functional transfer must keep gluing roots closed (or carry equivalent domain
and closure data).
-/

namespace StructuralRamsey.Structure.FunctionalTreeTransferObstruction

open StructuralRamsey
open RelStructure

noncomputable section

/-- One unary partial function and no ordinary relations. -/
def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 1

/-- The two-point partial-function structure with F(false) = {true}. -/
def base : Structure language Bool where
  rel R := Empty.elim R
  func _ x := {y | x (0 : Fin 1) = false ∧ y = true}

theorem base_singletonValued : base.SingletonValued := by
  intro F x y z hy hz
  change x (0 : Fin 1) = false ∧ y = true at hy
  change x (0 : Fin 1) = false ∧ z = true at hz
  exact hy.2.trans hz.2.symm

/-- The non-closed one-point root containing the input but not its output. -/
def root : RelStructure language.graph Unit where
  rel _ _ := False

/-- Both copies use the input vertex as their root. -/
def rootEmbedding : RelStructure.Embedding root base.graph where
  toFun _ := false
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := by
    intro R x
    constructor
    · intro h
      cases R with
      | inl R => exact Empty.elim R
      | inr F =>
          cases F
          change
            ((fun _ : Unit => false) ∘ x) (Fin.last 1) ∈
              base.func ()
                (fun i : Fin 1 =>
                  ((fun _ : Unit => false) ∘ x) (Fin.castSucc i)) at h
          change False
          have hout : ((fun _ : Unit => false) ∘ x) (Fin.last 1) = false := rfl
          have hin :
              ((fun _ : Unit => false) ∘ x) ((0 : Fin 1).castSucc) = false := rfl
          change
            ((fun _ : Unit => false) ∘ x) ((0 : Fin 1).castSucc) = false ∧
              ((fun _ : Unit => false) ∘ x) (Fin.last 1) = true at h
          exact Bool.noConfusion (hout.symm.trans h.2)
    · intro h
      exact False.elim h

def edgeTuple : Fin 2 → Bool := ![false, true]

theorem base_graph_edge :
    base.graph.rel (.inr ()) edgeTuple := by
  change edgeTuple (Fin.last 1) ∈
    base.func () (fun i : Fin 1 => edgeTuple (Fin.castSucc i))
  change
    edgeTuple ((0 : Fin 1).castSucc) = false ∧
      edgeTuple (Fin.last 1) = true
  decide

theorem base_graph_irreducible : base.graph.Irreducible := by
  intro x y hxy
  cases x <;> cases y
  · exact (hxy rfl).elim
  · refine ⟨(.inr () : language.graph.Symbol), edgeTuple,
      (0 : Fin 2), (1 : Fin 2), base_graph_edge, rfl, rfl⟩
  · refine ⟨(.inr () : language.graph.Symbol), edgeTuple,
      (1 : Fin 2), (0 : Fin 2), base_graph_edge, rfl, rfl⟩
  · exact (hxy rfl).elim

theorem root_contained :
    rootEmbedding.ContainedInIrreducible := by
  let e : RelStructure.Embedding base.graph base.graph :=
    RelStructure.Embedding.id base.graph
  refine ⟨Set.range e, base_graph_irreducible.range_embedding e, ?_⟩
  intro d
  exact ⟨rootEmbedding d, rfl⟩

abbrev TargetVertex :=
  RelStructure.FreeAmalgam.Vertex
    root base.graph base.graph rootEmbedding rootEmbedding

noncomputable def target : RelStructure language.graph TargetVertex :=
  RelStructure.FreeAmalgam.amalgam
    root base.graph base.graph rootEmbedding rootEmbedding

noncomputable def left :
    RelStructure.Embedding base.graph target :=
  RelStructure.FreeAmalgam.leftEmbedding
    root base.graph base.graph rootEmbedding rootEmbedding

noncomputable def right :
    RelStructure.Embedding base.graph target :=
  RelStructure.FreeAmalgam.rightEmbedding
    root base.graph base.graph rootEmbedding rootEmbedding

/-- The bad relational amalgam is nevertheless a strict tree amalgam of
copies of the graph encoding of the base. -/
theorem target_tree :
    RelStructure.TreeAmalgam base.graph TargetVertex target := by
  exact
    RelStructure.FreeAmalgam.treeAmalgam
      root base.graph base.graph rootEmbedding rootEmbedding base.graph
      (RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl base.graph))
      (RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl base.graph))
      root_contained root_contained

theorem common_input :
    left false = right false := by
  exact RelStructure.FreeAmalgam.left_right_overlap
    root base.graph base.graph rootEmbedding rootEmbedding ()

theorem left_output :
    left true ∈
      (Structure.ofGraph target).func () (fun _ : Fin 1 => left false) := by
  change
    target.rel (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => left false) (left true))
  have h :=
    (left.map_rel_iff (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => false) true)).2
      base_graph_edge
  have htuple :=
    Structure.comp_funcTuple
      (fun b : Bool => left b) (fun _ : Fin 1 => false) true
  have hrel :
      target.rel (.inr ())
        (Structure.funcTuple (fun _ : Fin 1 => left false) (left true)) := by
    simpa only [Function.comp_apply] using
      Eq.mp (congrArg (fun t => target.rel (.inr ()) t) htuple) h
  exact hrel

theorem right_output :
    right true ∈
      (Structure.ofGraph target).func () (fun _ : Fin 1 => left false) := by
  change
    target.rel (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => left false) (right true))
  have h :=
    (right.map_rel_iff (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => false) true)).2
      base_graph_edge
  have htuple :=
    Structure.comp_funcTuple
      (fun b : Bool => right b) (fun _ : Fin 1 => false) true
  have hrel :
      target.rel (.inr ())
        (Structure.funcTuple (fun _ : Fin 1 => right false) (right true)) := by
    simpa only [Function.comp_apply] using
      Eq.mp (congrArg (fun t => target.rel (.inr ()) t) htuple) h
  have hinput :
      (fun _ : Fin 1 => right false) =
        (fun _ : Fin 1 => left false) := by
    funext i
    exact common_input.symm
  simpa only [hinput] using hrel

theorem outputs_distinct : left true ≠ right true := by
  intro h
  have hover :=
    (RelStructure.FreeAmalgam.isFreeAmalgam
      root base.graph base.graph rootEmbedding rootEmbedding).overlap
      true true
  obtain ⟨d, hd, _⟩ := hover.mp h
  cases d
  change true = false at hd
  exact Bool.noConfusion hd

/-- Decoding the strict relational tree produces a non-singleton function
fibre, even though the base itself is singleton-valued. -/
theorem target_not_singletonValued :
    ¬ (Structure.ofGraph target).SingletonValued := by
  intro h
  have heq :=
    h () (fun _ : Fin 1 => left false) (left true) (right true)
      left_output right_output
  exact outputs_distinct heq

end
end StructuralRamsey.Structure.FunctionalTreeTransferObstruction

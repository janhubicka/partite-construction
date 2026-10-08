import PartiteConstruction.Functional.TreeTransferObstruction
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Iterated.TreeCompletion
import PartiteConstruction.Iterated.WeakFunctionalTreeCompletion

/-! # A closed functional test whose graph-tree completion is not full

A graph-tree completion of a genuine *closed* function structure need not be
a full function-language tree completion, even if the base graph is
irreducible.

For the unary partial function F(false)={true}, F(true)=empty, glue two
copies of the graph of the base over a singleton mapping to the *output*
of the first copy and the *input* of the second copy. The resulting
relational tree is a directed path of length two. Decoded as a genuine
set-valued-function structure, its **entire universe** is a closed
substructure and its graph plainly has a strict relational tree witness.

But the base has no directed function chain of length two. This property
is preserved by every full functional tree amalgam of its copies, since
all side maps are full embeddings. A full homomorphism from the path
into such a tree would carry the chain to another chain, a contradiction.

This does NOT invalidate the verified native EHN weak-size induction.
It shows why its final graph-tree witnesses cannot be promoted to
full-function trees using only the closedness of the *tested source*.
Additional target-root/output closure is a mathematical obligation.
-/

namespace StructuralRamsey.Structure.FunctionalClosedTestGraphObstruction

open StructuralRamsey
open StructuralRamsey.Structure.FunctionalTreeTransferObstruction

noncomputable section

universe v

/-- A function structure has no nontrivial directed chain of two values. -/
def NoTwoStep {X : Type v} (T : Structure language X) : Prop :=
  ∀ (a b c : X),
    b ∈ T.func () (fun _ : Fin 1 => a) →
    c ∈ T.func () (fun _ : Fin 1 => b) → False

theorem base_noTwoStep : NoTwoStep base := by
  intro a b c hab hbc
  change a = false ∧ b = true at hab
  change b = false ∧ c = true at hbc
  have hwrong : (true : Bool) = false := hab.2.symm.trans hbc.1
  exact Bool.noConfusion hwrong

/-- No-two-step is preserved under a union covered by two *full*
function embeddings; this uses only the covering clause of free
amalgamation and equality of function-image fibres under embeddings. -/
theorem noTwoStep_of_full_cover
    {X Y Z : Type v}
    {L : Structure language X}
    {R : Structure language Y}
    {T : Structure language Z}
    (hL : NoTwoStep L) (hR : NoTwoStep R)
    (iL : Structure.Embedding L T) (iR : Structure.Embedding R T)
    (hcover : ∀ z : Z,
      (∃ x : X, z = iL x) ∨ (∃ y : Y, z = iR y)) :
    NoTwoStep T := by
  intro x y z hxy hyz
  rcases hcover x with ⟨a, ha⟩ | ⟨a, ha⟩
  · subst x
    have hy : y ∈ Structure.imageSet iL
        (L.func () (fun _ : Fin 1 => a)) := by
      rw [iL.map_func () (fun _ : Fin 1 => a)]
      exact hxy
    obtain ⟨b, hb, hby⟩ := hy
    have hz : z ∈ Structure.imageSet iL
        (L.func () (fun _ : Fin 1 => b)) := by
      rw [iL.map_func () (fun _ : Fin 1 => b)]
      simpa only [← hby] using hyz
    obtain ⟨c, hc, _⟩ := hz
    exact hL a b c hb hc
  · subst x
    have hy : y ∈ Structure.imageSet iR
        (R.func () (fun _ : Fin 1 => a)) := by
      rw [iR.map_func () (fun _ : Fin 1 => a)]
      exact hxy
    obtain ⟨b, hb, hby⟩ := hy
    have hz : z ∈ Structure.imageSet iR
        (R.func () (fun _ : Fin 1 => b)) := by
      rw [iR.map_func () (fun _ : Fin 1 => b)]
      simpa only [← hby] using hyz
    obtain ⟨c, hc, _⟩ := hz
    exact hR a b c hb hc

/-- Every genuine full-function tree amalgam of copies of base has no
two-step function chain. -/
theorem fullTree_noTwoStep
    {X : Type v} {T : Structure language X}
    (hTree : Structure.TreeAmalgam base X T) :
    NoTwoStep T := by
  induction hTree with
  | copy e hsurj =>
      exact noTwoStep_of_full_cover base_noTwoStep base_noTwoStep
        e e (fun z => Or.inl (hsurj z))
  | @glue X Y Z W L R H T hL hR fL fR hcL hcR iL iR
      hfree ihL ihR =>
      exact noTwoStep_of_full_cover ihL ihR iL iR hfree.covers

/-- The singleton empty graph root may also be placed at the *output*
of the base's unary function. -/
def outputRootEmbedding : RelStructure.Embedding root base.graph where
  toFun := fun _ => true
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact Empty.elim R
    | inr F =>
        cases F
        change (true = false ∧ true = true) ↔ False
        decide

theorem outputRoot_contained :
    outputRootEmbedding.ContainedInIrreducible := by
  let e : RelStructure.Embedding base.graph base.graph :=
    RelStructure.Embedding.id base.graph
  refine ⟨Set.range e, base_graph_irreducible.range_embedding e, ?_⟩
  intro d
  exact ⟨outputRootEmbedding d, rfl⟩

/-- The first copy's output is identified with the second copy's input. -/
abbrev PathVertex :=
  RelStructure.FreeAmalgam.Vertex
    root base.graph base.graph outputRootEmbedding rootEmbedding

noncomputable def pathGraph : RelStructure language.graph PathVertex :=
  RelStructure.FreeAmalgam.amalgam
    root base.graph base.graph outputRootEmbedding rootEmbedding

noncomputable def left :
    RelStructure.Embedding base.graph pathGraph :=
  RelStructure.FreeAmalgam.leftEmbedding
    root base.graph base.graph outputRootEmbedding rootEmbedding

noncomputable def right :
    RelStructure.Embedding base.graph pathGraph :=
  RelStructure.FreeAmalgam.rightEmbedding
    root base.graph base.graph outputRootEmbedding rootEmbedding

theorem pathGraph_tree :
    RelStructure.TreeAmalgam base.graph PathVertex pathGraph := by
  exact RelStructure.FreeAmalgam.treeAmalgam
    root base.graph base.graph outputRootEmbedding rootEmbedding base.graph
    (RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl base.graph))
    (RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl base.graph))
    outputRoot_contained root_contained

theorem middle_eq : left true = right false := by
  exact RelStructure.FreeAmalgam.left_right_overlap
    root base.graph base.graph outputRootEmbedding rootEmbedding ()

theorem embedded_edge
    {X : Type v} {T : RelStructure language.graph X}
    (e : RelStructure.Embedding base.graph T) :
    T.rel (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => e false) (e true)) := by
  have h :=
    (e.map_rel_iff (.inr ())
      (Structure.funcTuple (fun _ : Fin 1 => false) true)).2
      base_graph_edge
  have htuple :=
    Structure.comp_funcTuple
      (fun b : Bool => e b) (fun _ : Fin 1 => false) true
  simpa only [Function.comp_const] using
    (Eq.mp (congrArg (fun t => T.rel (.inr ()) t) htuple) h)

theorem path_first_edge :
    left true ∈ (Structure.ofGraph pathGraph).func ()
      (fun _ : Fin 1 => left false) := by
  change pathGraph.rel (.inr ())
    (Structure.funcTuple (fun _ : Fin 1 => left false) (left true))
  exact embedded_edge left

theorem path_second_edge :
    right true ∈ (Structure.ofGraph pathGraph).func ()
      (fun _ : Fin 1 => left true) := by
  change pathGraph.rel (.inr ())
    (Structure.funcTuple (fun _ : Fin 1 => left true) (right true))
  have h := embedded_edge right
  have heq : (fun _ : Fin 1 => right false) =
      (fun _ : Fin 1 => left true) := by
    funext _
    exact middle_eq.symm
  simpa only [heq] using h

/-- The *whole source* is closed under its functions, and it is
weak-graph tree-completable, but has no full function-language
homomorphism-embedding into any genuine tree of B-copies. -/
theorem pathGraph_hasTreeCompletion :
    RelStructure.HasTreeCompletion base.graph
      (Structure.ofGraph pathGraph).graph := by
  exact ⟨PathVertex, pathGraph, pathGraph_tree, id,
    (Structure.ofGraphGraphEmbedding pathGraph).isHomomorphismEmbedding⟩

theorem path_no_fullTreeCompletion :
    ¬ Structure.HasTreeCompletion base
        (Structure.ofGraph pathGraph) := by
  rintro ⟨X, T, hTree, f, hf⟩
  have hchain := fullTree_noTwoStep hTree
  have h01 :
      f (left true) ∈ T.func ()
        (fun _ : Fin 1 => f (left false)) := by
    have hmem : f (left true) ∈ Structure.imageSet f
        ((Structure.ofGraph pathGraph).func ()
          (fun _ : Fin 1 => left false)) :=
      ⟨left true, path_first_edge, rfl⟩
    rw [hf.1.2 () (fun _ : Fin 1 => left false)] at hmem
    exact hmem
  have h12 :
      f (right true) ∈ T.func ()
        (fun _ : Fin 1 => f (left true)) := by
    have hmem : f (right true) ∈ Structure.imageSet f
        ((Structure.ofGraph pathGraph).func ()
          (fun _ : Fin 1 => left true)) :=
      ⟨right true, path_second_edge, rfl⟩
    rw [hf.1.2 () (fun _ : Fin 1 => left true)] at hmem
    exact hmem
  exact hchain (f (left false)) (f (left true)) (f (right true))
    h01 h12

/-- Source closedness plus graph-tree completability alone does **not**
imply the full-function tree conclusion. -/
theorem closedSource_graphCompletion_not_fullCompletion :
    (Structure.ofGraph pathGraph).IsClosed Set.univ ∧
    RelStructure.HasTreeCompletion base.graph
      (Structure.ofGraph pathGraph).graph ∧
    ¬ Structure.HasTreeCompletion base
      (Structure.ofGraph pathGraph) := by
  refine ⟨?_, pathGraph_hasTreeCompletion, path_no_fullTreeCompletion⟩
  intro F x hx y hy
  exact Set.mem_univ y

end
end StructuralRamsey.Structure.FunctionalClosedTestGraphObstruction

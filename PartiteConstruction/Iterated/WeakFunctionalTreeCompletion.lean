import PartiteConstruction.Iterated.InducedTraceTreeCompletion
import PartiteConstruction.Iterated.WeakLocalTreeLike
import PartiteConstruction.Structure.WeakSubstructure

/-! # Weak local completions for the functional iterated construction

The relevant local-size induction is on arbitrary vertex sets, not on their
function closures.  Restricting a set-valued function to a vertex set keeps
only outputs still in the set: this is exactly induced restriction of its
relational graph.  Consequently, the already verified relational local
tree-completion theorem is also a theorem about weak functional tests.

A full induced partite pass raises the available test size from n to n+1
when the fixed base has projected histories at size n.  Individual Picture
steps preserve the new size n+1; it does not increase at every attachment.

For a genuinely closed test the same conclusion applies to its full induced
function structure, but with the *relational graph* interpretation of the
completion.  A graph homomorphism-embedding need not be fibre-surjective,
and an arbitrary relational tree of function graphs need not decode to a
strict functional tree.  These extra closure issues must not be silently
deduced from the weak-size induction.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {V W : Type v}

/-- Local graph-tree completability tested on arbitrary weak substructures
of a set-valued-function structure.  No false full-function target map is
assumed. -/
def WeakLocallyTreeCompletable
    (Base : Structure L V) (C : Structure L W) (n : ℕ) : Prop :=
  RelStructure.LocallyTreeCompletable Base.graph C.graph n

/-- The unfolded weak formulation: at every bounded vertex set, function
outputs leaving the set are discarded, and the remaining graph admits a
relational tree completion. -/
theorem weakLocallyTreeCompletable_iff
    (Base : Structure L V) (C : Structure L W) (n : ℕ) :
    WeakLocallyTreeCompletable Base C n ↔
      ∀ S : Finset W, S.card ≤ n →
        ∃ (Y : Type v) (T : RelStructure L.graph Y),
          RelStructure.TreeAmalgam Base.graph Y T ∧
          ∃ f : ↥(↑S : Set W) → Y,
            (C.weakInduce (↑S : Set W)).graph.IsHomomorphismEmbedding
              T f := by
  constructor
  · intro h S hSize
    obtain ⟨Y, T, hTree, f, hf⟩ := h S hSize
    refine ⟨Y, T, hTree, f, ?_⟩
    exact hf.comp
      (weakGraphToInduce C (↑S : Set W)).isHomomorphismEmbedding
  · intro h S hSize
    obtain ⟨Y, T, hTree, f, hf⟩ := h S hSize
    refine ⟨Y, T, hTree, f, ?_⟩
    exact hf.comp
      (weakGraphFromInduce C (↑S : Set W)).isHomomorphismEmbedding

namespace WeakLocallyTreeCompletable

variable {Base : Structure L V} {C : Structure L W} {n : ℕ}

/-- The final passage to genuine closed substructures at the *graph*
level.  Closedness identifies the full induced function structure with
the weak restriction, and therefore does not change the vertex budget. -/
theorem closedTest_graphCompletion
    (h : WeakLocallyTreeCompletable Base C n)
    (S : Finset W) (hSize : S.card ≤ n)
    (hClosed : C.IsClosed (↑S : Set W)) :
    RelStructure.HasTreeCompletion Base.graph
      (C.induce (↑S : Set W) hClosed).graph := by
  obtain ⟨Y, T, hTree, f, hf⟩ := h S hSize
  let j : RelStructure.Embedding
      (C.induce (↑S : Set W) hClosed).graph
      (C.graph.induce (↑S : Set W)) :=
    (weakGraphToInduce C (↑S : Set W)).comp
      ((C.induceToWeak (↑S : Set W) hClosed).graph)
  exact ⟨Y, T, hTree, f ∘ j, hf.comp j.isHomomorphismEmbedding⟩

/-- Every controlled weak local-tree invariant already implies its
uncontrolled tree-completion conclusion. -/
theorem ofWeakLocallyTreeLike
    {U : Type v} {A : Structure L U}
    (h : WeakLocallyTreeLike A Base C n) :
    WeakLocallyTreeCompletable Base C n :=
  RelStructure.LocallyTreeCompletable.of_locallyTreeLike h

end WeakLocallyTreeCompletable

/-- The graph encoding of a decoded function structure is isomorphic to the
original relational graph, via the identity on vertices.  This elementary
embedding suffices to transfer all bounded weak tests from a relational
partite output to its functional interpretation. -/
def ofGraphGraphEmbedding
    {X : Type v} (R : RelStructure L.graph X) :
    RelStructure.Embedding (ofGraph R).graph R where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro Q x
    cases Q with
    | inl R0 =>
        exact Iff.rfl
    | inr F =>
        change
          R.rel (.inr F)
            (funcTuple
              (fun i : Fin (L.funcArity F) => x i.castSucc)
              (x (Fin.last (L.funcArity F)))) ↔ R.rel (.inr F) x
        rw [funcTuple_eta]

/-- Any relational local tree-completion theorem in the function-graph
language transfers to weak substructures of the decoded function structure.
There is no assertion here that relational gluing roots are function-closed. -/
theorem WeakLocallyTreeCompletable.ofGraph
    {X : Type v}
    (Base : Structure L V)
    (R : RelStructure L.graph X) (n : ℕ)
    (h : RelStructure.LocallyTreeCompletable Base.graph R n) :
    WeakLocallyTreeCompletable Base (ofGraph R) n :=
  h.pullback_embedding (ofGraphGraphEmbedding R)

end StructuralRamsey.Structure

namespace StructuralRamsey.Partite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v

variable {L : Language.{u}}
variable {U V P : Type v}

/-- One *full* induced partite construction raises weak graph-tree
completability by one vertex.  The input projected-history hypothesis
lives at level n, the output's weak tests at level n+1, and every
individual Picture step preserves level n+1. -/
theorem inducedConstruction_weakFunctionalTreeCompletable_succ
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A.graph B.graph D.graph κ)
    (hA : A.graph.Irreducible)
    (eAB : RelStructure.Embedding A.graph B.graph)
    (n : ℕ)
    (hD : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A.graph) (D := D.graph) (C := D.graph)
      (B := B.graph) id n) :
    letI : Nonempty (RelStructure.Embedding B.graph D.graph) :=
      nonempty_embedding_of_arrow A.graph B.graph D.graph κ hRamsey
    let S₀ := initialStage B.graph D.graph
    ∃ T : Stage B.graph D.graph,
      Trace A.graph B.graph D.graph S₀
        (allRelevant A.graph B.graph D.graph).reverse T ∧
      StructuralRamsey.Arrow A.graph B.graph
        T.system.toRelStructure κ ∧
      WeakLocallyTreeCompletable B
        (Structure.ofGraph T.system.toRelStructure) (n + 1) := by
  classical
  have hD' : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A.graph) (D := D.graph) (C := D.graph)
      (B := B.graph) id ((n + 1) - 1) := by
    simpa using hD
  obtain ⟨T, hTrace, hArrow, hLocal⟩ :=
    inducedConstruction_locallyTreeCompletable
      A.graph B.graph D.graph κ hRamsey hA eAB
      (n + 1) (by omega) hD'
  exact ⟨T, hTrace, hArrow,
    WeakLocallyTreeCompletable.ofGraph B
      T.system.toRelStructure (n + 1) hLocal⟩

end StructuralRamsey.Partite.Induced

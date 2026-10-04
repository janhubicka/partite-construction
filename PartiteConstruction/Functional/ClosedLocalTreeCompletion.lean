import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Closed local tree completions for function languages

For structures with set-valued functions, a genuine substructure is carried by
a function-closed set.  This file packages the local conclusion needed for the
functional sparsening theorem without silently replacing closed substructures
by weak induced subsets.

The global projection used by the functional partite construction may remain
weak.  The completion maps in this file are full homomorphism-embeddings and
the target trees are genuine function-language tree amalgams.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {V W X : Type v}

/-- A full relation/function structure admits a full homomorphism-embedding
into a genuine tree amalgam of copies of `Base`. -/
def HasTreeCompletion
    (Base : Structure L V) (C : Structure L W) : Prop :=
  ∃ (Y : Type v) (T : Structure L Y),
    TreeAmalgam Base Y T ∧
      ∃ f : W → Y, C.IsHomomorphismEmbedding T f

/-- Every *closed* substructure on at most `n` vertices has a full tree
completion.  The explicit `IsClosed` hypothesis is the function-language
meaning of "substructure" in the survey. -/
def LocallyClosedTreeCompletable
    (Base : Structure L V) (C : Structure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ hS : C.IsClosed (↑S : Set W),
      HasTreeCompletion Base (C.induce (↑S : Set W) hS)

namespace LocallyClosedTreeCompletable

variable {Base : Structure L V} {C : Structure L W}
variable {m n : ℕ}

/-- Monotonicity in the size bound. -/
theorem mono
    (h : LocallyClosedTreeCompletable Base C n) (hmn : m ≤ n) :
    LocallyClosedTreeCompletable Base C m := by
  intro S hS hclosed
  exact h S (hS.trans hmn) hclosed

/-- If the whole structure is already a tree amalgam of copies of the base,
then every closed finite substructure has the required completion, via its
full inclusion map. -/
theorem of_treeAmalgam
    (hTree : TreeAmalgam Base W C) (n : ℕ) :
    LocallyClosedTreeCompletable Base C n := by
  intro S _ hS
  let e : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  exact ⟨W, C, hTree, e, e.isHomomorphismEmbedding⟩

/-- One copy of the base is locally tree completable at every scale. -/
theorem base (Base : Structure L V) (n : ℕ) :
    LocallyClosedTreeCompletable Base Base n := by
  have hTree : TreeAmalgam Base V Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro x
      exact ⟨x, rfl⟩)
  exact of_treeAmalgam hTree n

end LocallyClosedTreeCompletable

/-- Function-closed subsets of the relational graph encoding are exactly
closed subsets in the original function structure. -/
theorem isClosed_iff_graph_functionClosedSet
    (A : Structure L W) (S : Set W) :
    A.IsClosed S ↔ RelStructure.FunctionClosedSet A.graph S := by
  constructor
  · intro h F x y hy hx
    apply h F x hx
    exact (graph_func_snoc A F x y).mp hy
  · intro h F x hx y hy
    apply h F x y
    · exact (graph_func_snoc A F x y).2 hy
    · exact hx

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure

/-- On a closed set, genuine functional induction and relational graph
induction are canonically identical. -/
def induceGraphIso
    (A : Structure L W) (S : Set W) (hS : A.IsClosed S) :
    RelStructure.Iso
      (A.induce S hS).graph
      (A.graph.induce S) where
  toEquiv := Equiv.refl S
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        rfl
    | inr F =>
        change
          A.graph.rel (.inr F) (Subtype.val ∘ x) ↔
            (x (Fin.last (L.funcArity F))).1 ∈
              A.func F
                (fun i =>
                  (x (Fin.castSucc i)).1)
        change
          (Subtype.val ∘ x) (Fin.last (L.funcArity F)) ∈
              A.func F
                (fun i => (Subtype.val ∘ x) (Fin.castSucc i)) ↔ _
        rfl

/-- A closed test set pulls back to a closed test set along any full
embedding; in particular this applies to the side embeddings of a free
amalgam. -/
theorem closed_preimage
    {A : Structure L V} {C : Structure L W}
    (e : Embedding A C) (S : Set W) (hS : C.IsClosed S) :
    A.IsClosed (e ⁻¹' S) :=
  e.preimage_isClosed S hS

end StructuralRamsey.Structure

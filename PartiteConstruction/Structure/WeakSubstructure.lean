import PartiteConstruction.Structure.Relationalize
import PartiteConstruction.Relational.Homomorphism

/-! # Weak substructures

For structures with set-valued functions an arbitrary vertex subset need not be
a (closed) substructure.  Its weak substructure keeps all relation tuples on
the subset and keeps exactly those function values which remain inside the
subset.  Equivalently, after replacing every function by its graph relation,
weak substructures are ordinary induced relational substructures.
-/
namespace StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Weak substructure induced by an arbitrary vertex set.  Function values
outside the chosen carrier are discarded; if all values leave the carrier the
function becomes undefined there. -/
def weakInduce (A : Structure L V) (S : Set V) : Structure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := {y | y.1 ∈ A.func F (Subtype.val ∘ x)}

@[simp] theorem weakInduce_rel (A : Structure L V) (S : Set V)
    (R : L.RelSymbol) (x : Fin (L.relArity R) → S) :
    (A.weakInduce S).rel R x ↔ A.rel R (Subtype.val ∘ x) :=
  Iff.rfl

@[simp] theorem weakInduce_func (A : Structure L V) (S : Set V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → S) (y : S) :
    y ∈ (A.weakInduce S).func F x ↔
      y.1 ∈ A.func F (Subtype.val ∘ x) :=
  Iff.rfl

/-- The graph encoding of a weak substructure has exactly the relations of the
ordinary induced relational substructure of the graph encoding. -/
theorem weakInduce_graph_rel_iff
    (A : Structure L V) (S : Set V)
    (R : L.graph.Symbol)
    (x : Fin (L.graph.arity R) → S) :
    (A.weakInduce S).graph.rel R x ↔
      (A.graph.induce S).rel R x := by
  cases R with
  | inl R =>
      rfl
  | inr F =>
      change
        (x (Fin.last (L.funcArity F))).1 ∈
            A.func F (fun i => (x (Fin.castSucc i)).1) ↔
          (Subtype.val ∘ x) (Fin.last (L.funcArity F)) ∈
            A.func F
              (fun i => (Subtype.val ∘ x) (Fin.castSucc i))
      rfl

/-- Identity embedding from the graph of the weak substructure to the induced
substructure of the graph encoding. -/
def weakGraphToInduce
    (A : Structure L V) (S : Set V) :
    RelStructure.Embedding (A.weakInduce S).graph (A.graph.induce S) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R x
    simpa using (weakInduce_graph_rel_iff A S R x).symm

/-- Identity embedding in the reverse direction. -/
def weakGraphFromInduce
    (A : Structure L V) (S : Set V) :
    RelStructure.Embedding (A.graph.induce S) (A.weakInduce S).graph where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R x
    simpa using weakInduce_graph_rel_iff A S R x

/-- The canonical inclusion of a weak substructure is a relational embedding
after graph encoding.  It need not be a full embedding of function
structures, precisely because the chosen set need not be closed. -/
def weakInclusion
    (A : Structure L V) (S : Set V) :
    RelStructure.Embedding (A.weakInduce S).graph A.graph :=
  (RelStructure.inclusion A.graph S).comp (weakGraphToInduce A S)

/-- Weak embeddings are induced embeddings of the graph encodings.  Thus they
preserve and reflect every relation and every function value whose output is
present, but they do not require the image to be closed under further function
values. -/
abbrev WeakEmbedding (A : Structure L V) (B : Structure L W) :=
  RelStructure.Embedding A.graph B.graph

/-- Weak homomorphism-embeddings are homomorphism-embeddings of the graph
encodings. -/
def IsWeakHomomorphismEmbedding
    (A : Structure L V) (B : Structure L W) (f : V → W) : Prop :=
  A.graph.IsHomomorphismEmbedding B.graph f

/-- Closed substructures are a special case: the old induced structure and the
weak induced structure are identical as full structures. -/
def induceToWeak
    (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    Embedding (A.induce S hS) (A.weakInduce S) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F x
    ext y
    constructor <;> intro hy
    · exact ⟨y, hy, rfl⟩
    · rcases hy with ⟨z, hz, hzy⟩
      simpa only using hzy ▸ hz

end StructuralRamsey.Structure

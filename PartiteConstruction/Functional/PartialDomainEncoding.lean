import PartiteConstruction.Functional.SingletonExpansion
import PartiteConstruction.Structure.Relationalize

/-! # Relational encoding of partial functions with explicit domains

The simplified graph encoding remembers only output tuples.  For recursive
partite constructions with closures this loses the root/domain information
used in the Hubicka--Nesetril closure description.

For a finite partial-function structure we therefore use two relations for
each function symbol F:
* a domain relation of arity arity(F), and
* the usual graph relation of arity arity(F)+1.

When the target functions are singleton-valued, an ordinary relational
embedding of this encoding already determines a full function embedding:
domain reflection gives existence of a source value, graph preservation maps
it to a target value, and singleton-valuedness gives uniqueness.
-/
namespace StructuralRamsey

universe u v w

namespace Language

/-- Relational language containing original relations, function-domain
relations, and function-graph relations. -/
def partialGraph (L : Language.{u}) : RelLanguage.{u} where
  Symbol := L.RelSymbol ⊕ (L.FuncSymbol ⊕ L.FuncSymbol)
  arity
    | .inl R => L.relArity R
    | .inr (.inl F) => L.funcArity F
    | .inr (.inr F) => L.funcArity F + 1

@[simp] theorem partialGraph_arity_rel
    (L : Language.{u}) (R : L.RelSymbol) :
    L.partialGraph.arity (.inl R) = L.relArity R := rfl

@[simp] theorem partialGraph_arity_domain
    (L : Language.{u}) (F : L.FuncSymbol) :
    L.partialGraph.arity (.inr (.inl F)) = L.funcArity F := rfl

@[simp] theorem partialGraph_arity_func
    (L : Language.{u}) (F : L.FuncSymbol) :
    L.partialGraph.arity (.inr (.inr F)) = L.funcArity F + 1 := rfl

end Language

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Domain/root relation of a set-valued function. -/
def InFunctionDomain
    (A : Structure L V)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) : Prop :=
  ∃ y, y ∈ A.func F x

/-- The faithful relational encoding for partial functions: original
relations, explicit function domains, and output graphs. -/
def partialGraph (A : Structure L V) :
    RelStructure L.partialGraph V where
  rel
    | .inl R, x => A.rel R x
    | .inr (.inl F), x => A.InFunctionDomain F x
    | .inr (.inr F), x =>
        x (Fin.last (L.funcArity F)) ∈
          A.func F (fun i => x (Fin.castSucc i))

@[simp] theorem partialGraph_rel
    (A : Structure L V)
    (R : L.RelSymbol) (x : Fin (L.relArity R) → V) :
    A.partialGraph.rel (.inl R) x ↔ A.rel R x := Iff.rfl

@[simp] theorem partialGraph_domain
    (A : Structure L V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    A.partialGraph.rel (.inr (.inl F)) x ↔
      A.InFunctionDomain F x := Iff.rfl

@[simp] theorem partialGraph_func
    (A : Structure L V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) (y : V) :
    A.partialGraph.rel (.inr (.inr F)) (funcTuple x y) ↔
      y ∈ A.func F x := by
  change
    (funcTuple x y) (Fin.last (L.funcArity F)) ∈
      A.func F (fun i => (funcTuple x y) (Fin.castSucc i)) ↔ _
  simp

namespace Embedding

/-- A full embedding preserves and reflects the explicit-domain relational
encoding. -/
def partialGraph
    {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) :
    RelStructure.Embedding A.partialGraph B.partialGraph where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        exact e.map_rel_iff R x
    | inr R =>
      cases R with
      | inl F =>
        change
          B.InFunctionDomain F (e ∘ x) ↔
            A.InFunctionDomain F x
        constructor
        · rintro ⟨y, hy⟩
          have hy' : y ∈ imageSet e (A.func F x) := by
            rw [e.map_func F x]
            exact hy
          rcases hy' with ⟨z, hz, rfl⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, hz⟩
          refine ⟨e z, ?_⟩
          have hz' : e z ∈ imageSet e (A.func F x) :=
            ⟨z, hz, rfl⟩
          rw [e.map_func F x] at hz'
          exact hz'
      | inr F =>
        change
          (e (x (Fin.last (L.funcArity F))) ∈
            B.func F
              (fun i => e (x (Fin.castSucc i)))) ↔
          (x (Fin.last (L.funcArity F)) ∈
            A.func F
              (fun i => x (Fin.castSucc i)))
        constructor
        · intro hy
          have hfun :
              (e ∘ (fun i : Fin (L.funcArity F) =>
                x (Fin.castSucc i))) =
                (fun i => e (x (Fin.castSucc i))) := by
            funext i
            rfl
          have hy' :
              e (x (Fin.last (L.funcArity F))) ∈
                B.func F
                  (e ∘ (fun i : Fin (L.funcArity F) =>
                    x (Fin.castSucc i))) := by
            rw [hfun]
            exact hy
          rw [← e.map_func F
            (fun i : Fin (L.funcArity F) =>
              x (Fin.castSucc i))] at hy'
          rcases hy' with ⟨z, hz, heq⟩
          exact e.injective heq ▸ hz
        · intro hy
          have himg :
              e (x (Fin.last (L.funcArity F))) ∈
                imageSet e
                  (A.func F
                    (fun i : Fin (L.funcArity F) =>
                      x (Fin.castSucc i))) :=
            ⟨_, hy, rfl⟩
          rw [e.map_func F
            (fun i : Fin (L.funcArity F) =>
              x (Fin.castSucc i))] at himg
          have hfun :
              (e ∘ (fun i : Fin (L.funcArity F) =>
                x (Fin.castSucc i))) =
                (fun i => e (x (Fin.castSucc i))) := by
            funext i
            rfl
          rw [hfun] at himg
          exact himg

@[simp] theorem partialGraph_apply
    {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) (x : V) :
    e.partialGraph x = e x := rfl

/-- An ordinary embedding of the domain+graph encoding into a
singleton-valued target is automatically a full function embedding. -/
def ofPartialGraph
    {A : Structure L V} {B : Structure L W}
    (hB : SingletonValued B)
    (e : RelStructure.Embedding A.partialGraph B.partialGraph) :
    Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    exact e.map_rel_iff (.inl R) x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hgraphA :
          A.partialGraph.rel (.inr (.inr F))
            (funcTuple x z) := by
        exact (Structure.partialGraph_func A F x z).2 hz
      have hgraphB0 :=
        (e.map_rel_iff (.inr (.inr F)) (funcTuple x z)).2 hgraphA
      have hcomp :
          e ∘ funcTuple x z =
            funcTuple (e ∘ x) (e z) :=
        Structure.comp_funcTuple e x z
      have hgraphB :
          B.partialGraph.rel (.inr (.inr F))
            (funcTuple (e ∘ x) (e z)) := by
        exact Eq.mp
          (congrArg
            (fun t => B.partialGraph.rel (.inr (.inr F)) t)
            hcomp)
          hgraphB0
      exact
        (Structure.partialGraph_func B F (e ∘ x) (e z)).1 hgraphB
    · intro hy
      have hdomB : B.InFunctionDomain F (e ∘ x) := ⟨y, hy⟩
      have hdomRelB :
          B.partialGraph.rel (.inr (.inl F)) (e ∘ x) := hdomB
      have hdomRelA :
          A.partialGraph.rel (.inr (.inl F)) x :=
        (e.map_rel_iff (.inr (.inl F)) x).1 hdomRelB
      rcases hdomRelA with ⟨z, hz⟩
      have hgraphA :
          A.partialGraph.rel (.inr (.inr F))
            (funcTuple x z) :=
        (Structure.partialGraph_func A F x z).2 hz
      have hgraphB0 :=
        (e.map_rel_iff (.inr (.inr F)) (funcTuple x z)).2 hgraphA
      have hcomp :
          e ∘ funcTuple x z =
            funcTuple (e ∘ x) (e z) :=
        Structure.comp_funcTuple e x z
      have hgraphB :
          B.partialGraph.rel (.inr (.inr F))
            (funcTuple (e ∘ x) (e z)) := by
        exact Eq.mp
          (congrArg
            (fun t => B.partialGraph.rel (.inr (.inr F)) t)
            hcomp)
          hgraphB0
      have hez : e z ∈ B.func F (e ∘ x) :=
        (Structure.partialGraph_func B F (e ∘ x) (e z)).1 hgraphB
      have hyz : y = e z := hB F (e ∘ x) y (e z) hy hez
      exact ⟨z, hz, hyz.symm⟩

@[simp] theorem ofPartialGraph_apply
    {A : Structure L V} {B : Structure L W}
    (hB : SingletonValued B)
    (e : RelStructure.Embedding A.partialGraph B.partialGraph)
    (x : V) :
    (Embedding.ofPartialGraph hB e) x = e x := rfl

/-- For singleton-valued targets, full embeddings are exactly ordinary
embeddings of the explicit-domain relational encoding. -/
def partialGraphEquiv
    {A : Structure L V} {B : Structure L W}
    (hB : SingletonValued B) :
    Embedding A B ≃
      RelStructure.Embedding A.partialGraph B.partialGraph where
  toFun := partialGraph
  invFun := ofPartialGraph hB
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.Embedding.ext
    intro x
    rfl

end Embedding

/-- In particular, after the ordered rank expansion every ordinary embedding
of the explicit-domain encoding lifts uniquely to a full embedding. -/
noncomputable def embeddingEquivRankedPartialGraph
    (A : Structure L V) (B : Structure L W)
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (n : ℕ) :
    Embedding (rankExpand A n) (rankExpand B n) ≃
      RelStructure.Embedding
        (rankExpand A n).partialGraph
        (rankExpand B n).partialGraph :=
  Embedding.partialGraphEquiv (rankExpand_singletonValued B n)

end Structure
end StructuralRamsey

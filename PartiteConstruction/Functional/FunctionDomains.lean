import PartiteConstruction.Functional.SingletonExpansion
import PartiteConstruction.Functional.Closed

/-! # Explicit function-domain relations and semi-closed structures

For the closure partite construction the input tuple of a partial function must
be visible relationally.  We add, for every function symbol F, an ordinary
relation symbol dom(F) of the same arity.  In a genuine structure dom(F)
holds exactly when the function fibre is nonempty.

For arbitrary relational graph structures in this expanded language we isolate
the two pieces of semi-closedness used by the recursive construction:
* every output tuple has its domain/root tuple;
* outputs are unique on the roots under consideration.

The intermediate little picture need not satisfy global uniqueness.  It is
enough that uniqueness holds on each relevant A-copy.
-/
namespace StructuralRamsey

universe u v w

namespace Language

/-- Add an ordinary relation naming the domain/root of every function symbol. -/
def withFunctionDomains (L : Language.{u}) : Language.{u} where
  RelSymbol := L.RelSymbol ⊕ L.FuncSymbol
  FuncSymbol := L.FuncSymbol
  relArity
    | .inl R => L.relArity R
    | .inr F => L.funcArity F
  funcArity := L.funcArity

@[simp] theorem withFunctionDomains_relArity_left
    (L : Language.{u}) (R : L.RelSymbol) :
    L.withFunctionDomains.relArity (.inl R) = L.relArity R := rfl

@[simp] theorem withFunctionDomains_relArity_domain
    (L : Language.{u}) (F : L.FuncSymbol) :
    L.withFunctionDomains.relArity (.inr F) = L.funcArity F := rfl

@[simp] theorem withFunctionDomains_funcArity
    (L : Language.{u}) (F : L.FuncSymbol) :
    L.withFunctionDomains.funcArity F = L.funcArity F := rfl

theorem PositiveFuncArity.withFunctionDomains
    {L : Language.{u}} (h : L.PositiveFuncArity) :
    L.withFunctionDomains.PositiveFuncArity :=
  h

end Language

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Add the canonical domain/root relations to a relation/function structure. -/
def withFunctionDomains (A : Structure L V) :
    Structure L.withFunctionDomains V where
  rel
    | .inl R, x => A.rel R x
    | .inr F, x => ∃ y, y ∈ A.func F x
  func F x := A.func F x

@[simp] theorem withFunctionDomains_rel
    (A : Structure L V) (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    A.withFunctionDomains.rel (.inl R) x ↔ A.rel R x :=
  Iff.rfl

@[simp] theorem withFunctionDomains_domain
    (A : Structure L V) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    A.withFunctionDomains.rel (.inr F) x ↔
      ∃ y, y ∈ A.func F x :=
  Iff.rfl

@[simp] theorem withFunctionDomains_func
    (A : Structure L V) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    A.withFunctionDomains.func F x = A.func F x :=
  rfl

namespace Embedding

/-- Full embeddings canonically lift after naming function domains. -/
def withFunctionDomains
    {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) :
    Embedding A.withFunctionDomains B.withFunctionDomains where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        exact e.map_rel_iff R x
    | inr F =>
        change
          (∃ y, y ∈ B.func F (e ∘ x)) ↔
            ∃ z, z ∈ A.func F x
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
  map_func := e.map_func

@[simp] theorem withFunctionDomains_apply
    {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) (x : V) :
    e.withFunctionDomains x = e x := rfl

end Embedding

end Structure

namespace RelStructure

open Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- In the domain-expanded graph language, every function-output tuple carries
its root/domain tuple. -/
def OutputImpliesDomain
    (A : RelStructure L.withFunctionDomains.graph V) : Prop :=
  ∀ (F : L.withFunctionDomains.FuncSymbol)
      (x : Fin (L.withFunctionDomains.funcArity F) → V) y,
    A.rel (.inr F) (funcTuple x y) →
      A.rel (.inl (.inr F)) x

/-- Every declared root/domain tuple has a function output.  Genuine
partial-function structures with their canonical domain relations satisfy this
by definition. -/
def FunctionDomainTotal
    (A : RelStructure L.withFunctionDomains.graph V) : Prop :=
  ∀ (F : L.withFunctionDomains.FuncSymbol)
      (x : Fin (L.withFunctionDomains.funcArity F) → V),
    A.rel (.inl (.inr F)) x →
      ∃ y, A.rel (.inr F) (funcTuple x y)

/-- Global semi-closedness for partial functions: output tuples have a root and
each root has at most one output.  Roots are allowed to have no output. -/
def FunctionSemiClosed
    (A : RelStructure L.withFunctionDomains.graph V) : Prop :=
  A.OutputImpliesDomain ∧
  ∀ (F : L.withFunctionDomains.FuncSymbol)
      (x : Fin (L.withFunctionDomains.funcArity F) → V) y z,
    A.rel (.inr F) (funcTuple x y) →
    A.rel (.inr F) (funcTuple x z) →
    y = z

/-- Local uniqueness of function outputs along one embedded copy.  This is the
property the sandwiched little picture retains even when it is not globally
semi-closed. -/
def LocallySingleValuedOn
    {U : Type v}
    (A : RelStructure L.withFunctionDomains.graph U)
    (B : RelStructure L.withFunctionDomains.graph V)
    (e : Embedding A B) : Prop :=
  ∀ (F : L.withFunctionDomains.FuncSymbol)
      (x : Fin (L.withFunctionDomains.funcArity F) → U) y z,
    B.rel (.inr F) (funcTuple (e ∘ x) y) →
    B.rel (.inr F) (funcTuple (e ∘ x) z) →
    y = z

/-- The canonical graph of a genuine domain-expanded structure has the
output-implies-domain property. -/
theorem withFunctionDomains_graph_outputImpliesDomain
    (A : Structure L V) :
    A.withFunctionDomains.graph.OutputImpliesDomain := by
  intro F x y hy
  have hy' :
      y ∈ A.withFunctionDomains.func F x :=
    (Structure.graph_func_snoc
      A.withFunctionDomains F x y).1 hy
  change y ∈ A.func F x at hy'
  change ∃ z, z ∈ A.func F x
  exact ⟨y, hy'⟩

/-- Canonical domain relations are total: a declared domain tuple has an
output. -/
theorem withFunctionDomains_graph_domainTotal
    (A : Structure L V) :
    A.withFunctionDomains.graph.FunctionDomainTotal := by
  intro F x hx
  change ∃ y, y ∈ A.func F x at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  exact
    (Structure.graph_func_snoc
      A.withFunctionDomains F x y).2 hy

/-- A singleton-valued genuine partial-function structure is semi-closed after
adding domain relations. -/
theorem withFunctionDomains_graph_semiClosed
    (A : Structure L V)
    (hA : A.SingletonValued) :
    A.withFunctionDomains.graph.FunctionSemiClosed := by
  refine
    ⟨withFunctionDomains_graph_outputImpliesDomain A, ?_⟩
  intro F x y z hy hz
  have hy' :
      y ∈ A.withFunctionDomains.func F x :=
    (Structure.graph_func_snoc
      A.withFunctionDomains F x y).1 hy
  have hz' :
      z ∈ A.withFunctionDomains.func F x :=
    (Structure.graph_func_snoc
      A.withFunctionDomains F x z).1 hz
  change y ∈ A.func F x at hy'
  change z ∈ A.func F x at hz'
  exact hA F x y z hy' hz'

/-- Domain reflection plus local output uniqueness upgrades an ordinary
embedding to a closed embedding.  This is the mechanism used after the
little-picture step. -/
def closedEmbedding_of_localSemiClosed
    {U : Type v}
    {A : RelStructure L.withFunctionDomains.graph U}
    {B : RelStructure L.withFunctionDomains.graph V}
    (hBroot : B.OutputImpliesDomain)
    (e : Embedding A B)
    (hLocal : LocallySingleValuedOn A B e)
    (hAtotal : A.FunctionDomainTotal) :
    ClosedEmbedding A B := by
  refine ⟨e, ?_⟩
  intro F x y hy
  have hdomB :
      B.rel (.inl (.inr F)) (e ∘ x) :=
    hBroot F (e ∘ x) y hy
  have hdomA :
      A.rel (.inl (.inr F)) x :=
    (e.map_rel_iff (.inl (.inr F)) x).mp hdomB
  obtain ⟨z, hz⟩ := hAtotal F x hdomA
  have hez :
      B.rel (.inr F)
        (funcTuple (e ∘ x) (e z)) := by
    have hz' :=
      (e.map_rel_iff (.inr F)
        (funcTuple x z)).mpr hz
    have ht :
        e ∘ funcTuple x z =
          funcTuple (e ∘ x) (e z) :=
      Structure.comp_funcTuple e x z
    exact Eq.mp
      (congrArg
        (fun t => B.rel (.inr F) t) ht)
      hz'
  have heq : y = e z :=
    hLocal F x y (e z) hy hez
  exact ⟨z, hz, heq.symm⟩

end RelStructure
end StructuralRamsey

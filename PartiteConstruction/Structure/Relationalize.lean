import PartiteConstruction.Structure.Basic
import PartiteConstruction.Relational.Homomorphism
import Mathlib.Data.Fin.Tuple.Basic

/-! # Relational graph encoding of set-valued functions

Each function symbol F of arity n is represented by an (n+1)-ary relation
holding on (x_0,...,x_{n-1},y) exactly when y belongs to F(x_0,...,x_{n-1}).
Full embeddings are precisely relational graph embeddings whose image is
closed under all function-value relations.
-/
namespace StructuralRamsey

universe u v w

namespace Language

def graph (L : Language.{u}) : RelLanguage.{u} where
  Symbol := Sum L.RelSymbol L.FuncSymbol
  arity
    | .inl R => L.relArity R
    | .inr F => L.funcArity F + 1

end Language

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Append a function value as the last coordinate of its graph tuple. -/
def funcTuple {n : ℕ} (x : Fin n → V) (y : V) : Fin (n + 1) → V :=
  Fin.lastCases y x

@[simp] theorem funcTuple_last {n : ℕ} (x : Fin n → V) (y : V) :
    funcTuple x y (Fin.last n) = y := by
  simp [funcTuple]

@[simp] theorem funcTuple_castSucc {n : ℕ} (x : Fin n → V) (y : V)
    (i : Fin n) :
    funcTuple x y i.castSucc = x i := by
  simp [funcTuple]

def graph (A : Structure L V) : RelStructure L.graph V where
  rel
    | .inl R, x => A.rel R x
    | .inr F, x =>
        x (Fin.last (L.funcArity F)) ∈
          A.func F (fun i => x i.castSucc)

/-- Reconstruct a relation/function structure from an arbitrary relational
structure in the graph language. -/
def ofGraph (R : RelStructure L.graph V) : Structure L V where
  rel S x := R.rel (.inl S) x
  func F x := {y | R.rel (.inr F) (funcTuple x y)}

@[simp] theorem ofGraph_rel (R : RelStructure L.graph V)
    (S : L.RelSymbol) (x : Fin (L.relArity S) → V) :
    (ofGraph R).rel S x ↔ R.rel (.inl S) x := Iff.rfl

@[simp] theorem ofGraph_func (R : RelStructure L.graph V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) (y : V) :
    y ∈ (ofGraph R).func F x ↔ R.rel (.inr F) (funcTuple x y) := Iff.rfl

/-- Relational graph membership for a function tuple built by snoc. -/
@[simp] theorem graph_func_snoc (A : Structure L V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) (y : V) :
    A.graph.rel (.inr F) (funcTuple x y) ↔ y ∈ A.func F x := by
  change (funcTuple x y) (Fin.last (L.funcArity F)) ∈
    A.func F (fun i => (funcTuple x y) i.castSucc) ↔ _
  simp


/-- The target contains no function value over an image tuple outside the
image of the source function value set. -/
def ClosedMap (A : Structure L V) (B : Structure L W) (f : V → W) : Prop :=
  ∀ F x y, y ∈ B.func F (f ∘ x) →
    ∃ z, z ∈ A.func F x ∧ f z = y

theorem IsHomomorphism.closedMap
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (h : A.IsHomomorphism B f) : A.ClosedMap B f := by
  intro F x y hy
  rw [← h.2 F x] at hy
  exact hy

namespace ClosedMap

variable {X : Type*} {A : Structure L V} {B : Structure L W}
  {C : Structure L X} {f : V → W} {g : W → X}

theorem comp (hg : B.ClosedMap C g) (hf : A.ClosedMap B f) :
    A.ClosedMap C (g ∘ f) := by
  intro F x y hy
  have hy' : y ∈ C.func F (g ∘ (f ∘ x)) := by
    simpa [Function.comp_assoc] using hy
  obtain ⟨b, hb, hby⟩ := hg F (f ∘ x) y hy'
  obtain ⟨a, ha, hab⟩ := hf F x b hb
  refine ⟨a, ha, ?_⟩
  change g (f a) = y
  rw [hab, hby]

end ClosedMap


theorem IsHomomorphism.graph
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (h : A.IsHomomorphism B f) :
    RelStructure.IsHomomorphism A.graph B.graph f := by
  intro R x hx
  cases R with
  | inl R =>
      exact h.1 R x hx
  | inr F =>
      change f (x (Fin.last (L.funcArity F))) ∈
        B.func F (fun i => f (x i.castSucc))
      have hs : x (Fin.last (L.funcArity F)) ∈
          A.func F (fun i => x i.castSucc) := hx
      have himg :
          f (x (Fin.last (L.funcArity F))) ∈
            imageSet f (A.func F (fun i => x i.castSucc)) :=
        ⟨_, hs, rfl⟩
      rw [h.2 F (fun i => x i.castSucc)] at himg
      have hfun :
          (f ∘ (fun i => x i.castSucc)) =
            (fun i => f (x i.castSucc)) := by
        funext i
        rfl
      rw [hfun] at himg
      exact himg

namespace Embedding

variable {A : Structure L V} {B : Structure L W}

/-- Every full embedding gives an induced embedding of the relational graph. -/
def graph (e : Embedding A B) : RelStructure.Embedding A.graph B.graph where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        exact e.map_rel_iff R x
    | inr F =>
        change
          (e (x (Fin.last (L.funcArity F))) ∈
            B.func F (fun i => e (x i.castSucc))) ↔
          (x (Fin.last (L.funcArity F)) ∈
            A.func F (fun i => x i.castSucc))
        constructor
        · intro hy
          have hfun :
              (e ∘ (fun i => x i.castSucc)) =
                (fun i => e (x i.castSucc)) := by
            funext i
            rfl
          have hy' : e (x (Fin.last (L.funcArity F))) ∈
              B.func F (e ∘ (fun i => x i.castSucc)) := by
            rw [hfun]
            exact hy
          rw [← e.map_func F (fun i => x i.castSucc)] at hy'
          rcases hy' with ⟨z, hz, heq⟩
          exact e.injective heq ▸ hz
        · intro hy
          have himg :
              e (x (Fin.last (L.funcArity F))) ∈
                imageSet e (A.func F (fun i => x i.castSucc)) :=
            ⟨_, hy, rfl⟩
          rw [e.map_func F (fun i => x i.castSucc)] at himg
          have hfun :
              (e ∘ (fun i => x i.castSucc)) =
                (fun i => e (x i.castSucc)) := by
            funext i
            rfl
          rw [hfun] at himg
          exact himg

/-- A relational graph embedding with function-closed image reconstructs the
full set-valued-function embedding. -/
def ofGraphClosed
    (e : RelStructure.Embedding A.graph B.graph)
    (hclosed : A.ClosedMap B e) :
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
      let t : Fin (L.funcArity F + 1) → V := funcTuple x z
      have ht : A.graph.rel (.inr F) t := by
        change t (Fin.last (L.funcArity F)) ∈
          A.func F (fun i => t i.castSucc)
        change z ∈ A.func F x
        exact hz
      have htarget := (e.map_rel_iff (.inr F) t).mpr ht
      change
        e (t (Fin.last (L.funcArity F))) ∈
          B.func F (fun i => e (t i.castSucc)) at htarget
      have htarget' : e z ∈ B.func F (fun i => e (x i)) := by
        simpa [t, funcTuple] using htarget
      have hfun : (e ∘ x) = (fun i => e (x i)) := by
        funext i
        rfl
      rw [hfun]
      exact htarget'
    · intro hy
      exact hclosed F x y hy

end Embedding
end Structure
end StructuralRamsey

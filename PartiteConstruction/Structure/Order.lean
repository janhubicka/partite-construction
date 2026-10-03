import PartiteConstruction.Functional.FunctionDomains
import PartiteConstruction.Relational.Order

/-! # Orders and reducts for structures with set-valued functions

Completing the distinguished order changes no function values.  Full
embeddings from ordered sources therefore survive order completion, and so
does the structural Ramsey arrow.  Canonically named function domains can
also be forgotten without changing the full-embedding Ramsey problem.
-/
namespace StructuralRamsey

universe u v w z

/-- Add a fresh binary order symbol without changing the function symbols. -/
def Language.withLinearOrder (L : Language.{u}) : Language.{u} where
  RelSymbol := L.RelSymbol ⊕ Unit
  FuncSymbol := L.FuncSymbol
  relArity := Sum.elim L.relArity (fun _ => 2)
  funcArity := L.funcArity

theorem Language.PositiveFuncArity.withLinearOrder
    {L : Language.{u}} (h : L.PositiveFuncArity) :
    L.withLinearOrder.PositiveFuncArity := h

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w} {X : Type z}

/-- Expand a structure by its given strict order. -/
def withLinearOrder (A : Structure L V) [LT V] :
    Structure L.withLinearOrder V where
  rel
    | .inl R, x => A.rel R x
    | .inr _, x => x 0 < x 1
  func := A.func

/-- Forget only the distinguished order symbol. -/
def linearOrderReduct (C : Structure L.withLinearOrder W) : Structure L W where
  rel R := C.rel (.inl R)
  func := C.func

/-- Forget the named domain relations, keeping every function fibre. -/
def functionDomainReduct (C : Structure L.withFunctionDomains W) :
    Structure L W where
  rel R := C.rel (.inl R)
  func := C.func

namespace Embedding

/-- Full embeddings between ordered expansions are strictly monotone. -/
theorem strictMono
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W]
    (e : Embedding A.withLinearOrder B.withLinearOrder) : StrictMono e := by
  intro x y hxy
  have h := (e.map_rel_iff (.inr ()) ![x, y]).mpr hxy
  exact h

/-- Forget the canonical domain predicates on the source and arbitrary domain
predicates on the target.  Full preservation of function fibres is unchanged. -/
def forgetFunctionDomains
    {A : Structure L V} {C : Structure L.withFunctionDomains W}
    (e : Embedding A.withFunctionDomains C) :
    Embedding A C.functionDomainReduct where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff (.inl R) x
  map_func := e.map_func

/-- Complete the order on the target while retaining full embeddings from a
linearly ordered source. -/
def completeLinearOrder
    {A : Structure L V} [LinearOrder V]
    {C : Structure L.withLinearOrder W} [LinearOrder W]
    (hC : ∀ x y, C.rel (.inr ()) ![x, y] → x < y)
    (e : Embedding A.withLinearOrder C) :
    Embedding A.withLinearOrder C.linearOrderReduct.withLinearOrder := by
  have hm : StrictMono e := by
    intro x y hxy
    apply hC
    have h := (e.map_rel_iff (.inr ()) ![x, y]).mpr hxy
    have heq : e ∘ ![x, y] = ![e x, e y] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp (congrArg (C.rel (.inr ())) heq) h
  exact {
    toFun := e
    injective := e.injective
    map_rel_iff := fun R x => by
      cases R with
      | inl R => exact e.map_rel_iff (.inl R) x
      | inr _ => exact hm.lt_iff_lt
    map_func := e.map_func
  }

end Embedding

/-- Canonical domain predicates do not alter the full-embedding Ramsey arrow. -/
theorem arrow_forgetFunctionDomains
    (A : Structure L V) (B : Structure L W)
    (C : Structure L.withFunctionDomains X) (κ : Type*)
    (h : Arrow A.withFunctionDomains B.withFunctionDomains C κ) :
    Arrow A B C.functionDomainReduct κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ e.forgetFunctionDomains)
  refine ⟨f.forgetFunctionDomains, ?_⟩
  intro e₁ e₂
  exact hf e₁.withFunctionDomains e₂.withFunctionDomains

/-- Order completion preserves the full structural Ramsey arrow. -/
theorem arrow_completeLinearOrder
    (A : Structure L V) (B : Structure L W)
    [LinearOrder V] [LinearOrder W]
    (C : Structure L.withLinearOrder X) [LinearOrder X]
    (hC : ∀ x y, C.rel (.inr ()) ![x, y] → x < y)
    (κ : Type*) (h : Arrow A.withLinearOrder B.withLinearOrder C κ) :
    Arrow A.withLinearOrder B.withLinearOrder
      C.linearOrderReduct.withLinearOrder κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ (e.completeLinearOrder hC))
  refine ⟨f.completeLinearOrder hC, ?_⟩
  intro e₁ e₂
  exact hf e₁ e₂

/-- A finite partite order has a linear extension, with arbitrary ordering
inside each part. -/
theorem exists_linearOrder_extension
    {P : Type*} [LinearOrder P] [Finite W]
    (C : Structure L.withLinearOrder W) (part : W → P)
    (hpart : ∀ x y, C.rel (.inr ()) ![x, y] → part x < part y) :
    ∃ o : LinearOrder W,
      ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt W o.toLT x y := by
  let R : RelStructure L.graph.withOrder W := {
    rel := fun S x => by
      cases S with
      | inl S => exact C.linearOrderReduct.graph.rel S x
      | inr _ => exact C.rel (.inr ()) x
  }
  obtain ⟨o, ho⟩ := RelStructure.exists_order_extension R part hpart
  exact ⟨o, ho⟩

end Structure
end StructuralRamsey

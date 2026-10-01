import PartiteConstruction.Ramsey.Basic
import Mathlib.Order.Prod.Lex.Basic

/-! # Adding and completing a distinguished order relation

The order is a fresh binary symbol. Completing its interpretation preserves
induced embeddings from linearly ordered sources. This is stronger than merely
showing that the old order is acyclic: it verifies the Ramsey arrow survives.
-/
namespace StructuralRamsey

universe u v w z

def RelLanguage.withOrder (L : RelLanguage.{u}) : RelLanguage.{u} where
  Symbol := L.Symbol ⊕ Unit
  arity := Sum.elim L.arity (fun _ => 2)

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w} {U : Type z}

def ordered (A : RelStructure L V) [LT V] : RelStructure L.withOrder V where
  rel R := by
    cases R with
    | inl R => exact A.rel R
    | inr _ => exact fun (x : Fin 2 → V) => x 0 < x 1

def orderReduct (C : RelStructure L.withOrder W) : RelStructure L W where
  rel R := C.rel (.inl R)

def completeOrder (C : RelStructure L.withOrder W) [LT W] : RelStructure L.withOrder W :=
  C.orderReduct.ordered

def ExtendsOrder (C : RelStructure L.withOrder W) [LT W] : Prop :=
  ∀ x y, C.rel (.inr ()) ![x, y] → x < y

namespace Embedding

def completeOrder {A : RelStructure L V} [LinearOrder V]
    {C : RelStructure L.withOrder W} [LinearOrder W]
    (hC : C.ExtendsOrder) (f : Embedding A.ordered C) :
    Embedding A.ordered C.completeOrder := by
  have hm : StrictMono f := by
    intro x y hxy
    apply hC
    have h := (f.map_rel_iff (.inr ()) ![x, y]).mpr hxy
    have heq : f ∘ ![x, y] = ![f x, f y] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp (congrArg (C.rel (.inr ())) heq) h
  exact {
    toFun := f
    injective := f.injective
    map_rel_iff := fun R x => by
      cases R with
      | inl R => exact f.map_rel_iff (.inl R) x
      | inr r => exact hm.lt_iff_lt
  }

end Embedding

theorem arrow_completeOrder (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] (C : RelStructure L.withOrder W) [LinearOrder W]
    (hC : C.ExtendsOrder) (κ : Type*) (h : Arrow A.ordered B.ordered C κ) :
    Arrow A.ordered B.ordered C.completeOrder κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun e => χ (e.completeOrder hC))
  refine ⟨f.completeOrder hC, ?_⟩
  intro e₁ e₂
  exact hf e₁ e₂

/-- A finite carrier can be ordered lexicographically by its partition label
and an arbitrary numbering inside each part. -/
theorem exists_order_extension {P : Type*} [LinearOrder P] [Finite W]
    (C : RelStructure L.withOrder W) (part : W → P)
    (hpart : ∀ x y, C.rel (.inr ()) ![x, y] → part x < part y) :
    ∃ o : LinearOrder W, @ExtendsOrder L W C o.toLT := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let key : W → P ×ₗ Fin (Fintype.card W) := fun x => toLex (part x, Fintype.equivFin W x)
  have hinj : Function.Injective key := by
    intro x y h
    exact (Fintype.equivFin W).injective (congrArg (fun p => (ofLex p).2) h)
  let o : LinearOrder W := LinearOrder.lift' key hinj
  refine ⟨o, ?_⟩
  intro x y hxy
  change key x < key y
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hpart x y hxy))

end RelStructure
end StructuralRamsey

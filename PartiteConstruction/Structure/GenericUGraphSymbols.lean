import PartiteConstruction.Structure.GenericUReducedLanguage
import PartiteConstruction.Structure.Relationalize

/-!
# The original relational signature is the graph of its reduced U-encoding

For an arbitrary relational L and distinguished U, the mixed language
L.withUFunctionsReduced U has ordinary relation symbols R not in U and a
set-valued function for every R in U. Its relational graph therefore has
exactly one symbol for each ORIGINAL relation, never a duplicate.

This module establishes the literal symbol equivalence and arity transport.
It is the first independent partite-system reindexing step needed to move the
verified function-graph Hales--Jewett/Picture constructions to arbitrary (L,U).
No partite Ramsey lemma is asserted here.
-/

namespace StructuralRamsey
universe u

namespace RelLanguage

/-- Interpret an original relation as either an unchanged ordinary relation
or the UNIQUE graph relation of its corresponding set-valued function. -/
def toReducedUGraphSymbol
    (L : RelLanguage.{u}) (U : Set L.Symbol) (R : L.Symbol) :
    (L.withUFunctionsReduced U).graph.Symbol := by
  classical
  exact if h : R ∈ U then Sum.inr (⟨R, h⟩ : U)
    else Sum.inl (⟨R, h⟩ : {S : L.Symbol // S ∉ U})

/-- Recover the original relation symbol from either side of the reduced
language's graph signature. -/
def fromReducedUGraphSymbol
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (S : (L.withUFunctionsReduced U).graph.Symbol) : L.Symbol :=
  match S with
  | .inl R => R.1
  | .inr R => R.1

@[simp] theorem from_toReducedUGraphSymbol
    (L : RelLanguage.{u}) (U : Set L.Symbol) (R : L.Symbol) :
    L.fromReducedUGraphSymbol U (L.toReducedUGraphSymbol U R) = R := by
  classical
  by_cases h : R ∈ U
  · simp [fromReducedUGraphSymbol, toReducedUGraphSymbol, h]
  · simp [fromReducedUGraphSymbol, toReducedUGraphSymbol, h]

@[simp] theorem to_fromReducedUGraphSymbol
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (S : (L.withUFunctionsReduced U).graph.Symbol) :
    L.toReducedUGraphSymbol U (L.fromReducedUGraphSymbol U S) = S := by
  classical
  cases S with
  | inl R =>
      have h : R.1 ∉ U := R.2
      simp [fromReducedUGraphSymbol, toReducedUGraphSymbol, h]
  | inr F =>
      have h : F.1 ∈ U := F.2
      simp [fromReducedUGraphSymbol, toReducedUGraphSymbol, h]

/-- Symbol-level equivalence between the original arbitrary relational L
and the graph of the nonredundant set-valued U-function encoding. -/
def reducedUGraphSymbolEquiv
    (L : RelLanguage.{u}) (U : Set L.Symbol) :
    L.Symbol ≃ (L.withUFunctionsReduced U).graph.Symbol where
  toFun := L.toReducedUGraphSymbol U
  invFun := L.fromReducedUGraphSymbol U
  left_inv := L.from_toReducedUGraphSymbol U
  right_inv := L.to_fromReducedUGraphSymbol U

/-- For distinguished U symbols of positive arity, the graph of an
(arity R - 1)-input function has arity EXACTLY arity R. Other relations
are preserved without change, including nullary symbols. -/
theorem reducedUGraphSymbol_arity
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (R : L.Symbol) :
    (L.withUFunctionsReduced U).graph.arity
      (L.toReducedUGraphSymbol U R) = L.arity R := by
  classical
  by_cases h : R ∈ U
  · simp only [toReducedUGraphSymbol, dif_pos h]
    change L.arity R - 1 + 1 = L.arity R
    exact Nat.sub_add_cancel (hU R h)
  · simp [toReducedUGraphSymbol, h, Language.graph,
      withUFunctionsReduced]

end RelLanguage
end StructuralRamsey

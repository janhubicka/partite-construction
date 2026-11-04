import PartiteConstruction.Structure.GenericUFunctionalDictionary

/-!
# Nonredundant U-relation / set-valued-function presentation

For Ramsey witnesses, retaining an original U-relation AND adding a new
function for it is unsafe: the two symbols can diverge in an arbitrary
functional target. This module therefore replaces each U-relation with its
set-valued function, retaining ONLY the non-U relations.

The two presentations have the same carriers and are inverse on arbitrary
structures. The ordered Ramsey transfer additionally has to remove a
distinguished order relation and reconstruct it from the witness order.
-/

namespace StructuralRamsey

universe u v

namespace RelLanguage

/-- Canonical mixed language: a non-U relation remains relational; a
U-relation R of arity m is represented only by a function of arity m-1. -/
def withUFunctionsReduced (L : RelLanguage.{u}) (U : Set L.Symbol) :
    Language.{u} where
  RelSymbol := {R : L.Symbol // R ∉ U}
  FuncSymbol := U
  relArity := fun R => L.arity R.1
  funcArity := fun F => L.arity F.1 - 1

theorem withUFunctionsReduced_positive
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R) :
    (L.withUFunctionsReduced U).PositiveFuncArity := by
  intro F
  change 0 < L.arity F.1 - 1
  have h := hU F.1 F.2
  omega

/-- Inputs of the relation obtained by deleting its final coordinate. -/
def rootU (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (t : Fin (L.arity F.1) → V) :
    Fin (L.arity F.1 - 1) → V :=
  fun i => t (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)) i.castSucc)

/-- Last coordinate, which is the value of the translated function. -/
def lastU (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (t : Fin (L.arity F.1) → V) : V :=
  t (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2))
    (Fin.last (L.arity F.1 - 1)))

@[simp] theorem rootU_append
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    rootU L U hU F (appendU L U hU F x y) = x := by
  funext i
  have h := Nat.sub_add_cancel (hU F.1 F.2)
  change Structure.funcTuple x y
    (Fin.cast h.symm (Fin.cast h i.castSucc)) = x i
  have hc : Fin.cast h.symm (Fin.cast h i.castSucc) = i.castSucc :=
    Fin.ext rfl
  rw [hc]
  exact Structure.funcTuple_castSucc x y i

@[simp] theorem lastU_append
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    lastU L U hU F (appendU L U hU F x y) = y := by
  have h := Nat.sub_add_cancel (hU F.1 F.2)
  change Structure.funcTuple x y
    (Fin.cast h.symm (Fin.cast h (Fin.last (L.arity F.1 - 1)))) = y
  have hc : Fin.cast h.symm
    (Fin.cast h (Fin.last (L.arity F.1 - 1))) =
      Fin.last (L.arity F.1 - 1) := Fin.ext rfl
  rw [hc]
  exact Structure.funcTuple_last x y

@[simp] theorem appendU_root_last
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (t : Fin (L.arity F.1) → V) :
    appendU L U hU F (rootU L U hU F t)
      (lastU L U hU F t) = t := by
  funext i
  have h := Nat.sub_add_cancel (hU F.1 F.2)
  let q : Fin (L.arity F.1 - 1 + 1) → V :=
    fun j => t (Fin.cast h j)
  change Structure.funcTuple (fun j => q j.castSucc)
    (q (Fin.last (L.arity F.1 - 1))) (Fin.cast h.symm i) = t i
  rw [Structure.funcTuple_eta q]
  have hc : Fin.cast h (Fin.cast h.symm i) = i := Fin.ext rfl
  exact congrArg t hc

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v}

/-- Encode the genuine original relations, with NO duplicate U relation. -/
def asUFunctionsReduced (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    Structure (L.withUFunctionsReduced U) V where
  rel R x := A.rel R.1 x
  func F x := {y | A.rel F.1 (RelLanguage.appendU L U hU F x y)}

end RelStructure

namespace Structure

variable {L : RelLanguage.{u}} {V : Type v}

/-- Decode an arbitrary mixed-language witness, taking each U-relation
ONLY from the function value set; no coherence assumption is needed. -/
def toRelU (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V) : RelStructure L V where
  rel R x :=
    if hr : R ∈ U then
      let F : U := ⟨R, hr⟩
      RelLanguage.lastU L U hU F x ∈
        C.func F (RelLanguage.rootU L U hU F x)
    else
      C.rel ⟨R, hr⟩ x

end Structure

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v}

theorem toRelU_asUFunctionsReduced_rel_iff
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (R : L.Symbol) (x : Fin (L.arity R) → V) :
    (Structure.toRelU U hU (A.asUFunctionsReduced U hU)).rel R x ↔
      A.rel R x := by
  by_cases h : R ∈ U
  · let F : U := ⟨R, h⟩
    change A.rel R
      (RelLanguage.appendU L U hU F
        (RelLanguage.rootU L U hU F x)
        (RelLanguage.lastU L U hU F x)) ↔ A.rel R x
    rw [RelLanguage.appendU_root_last]
  · change A.rel R x ↔ A.rel R x
    rfl

end RelStructure

namespace Structure

variable {L : RelLanguage.{u}} {V : Type v}

theorem asUFunctionsReduced_toRelU_rel_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V)
    (R : (L.withUFunctionsReduced U).RelSymbol)
    (x : Fin ((L.withUFunctionsReduced U).relArity R) → V) :
    (RelStructure.asUFunctionsReduced (toRelU U hU C) U hU).rel R x ↔
      C.rel R x := by
  change (if h : R.1 ∈ U then _ else C.rel ⟨R.1, h⟩ x) ↔ C.rel R x
  simp [R.2]

theorem asUFunctionsReduced_toRelU_func_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V)
    (F : (L.withUFunctionsReduced U).FuncSymbol)
    (x : Fin ((L.withUFunctionsReduced U).funcArity F) → V)
    (y : V) :
    y ∈ (RelStructure.asUFunctionsReduced (toRelU U hU C) U hU).func F x ↔
      y ∈ C.func F x := by
  change
    (if h : F.1 ∈ U then
      RelLanguage.lastU L U hU ⟨F.1, h⟩
        (RelLanguage.appendU L U hU F x y) ∈
        C.func ⟨F.1, h⟩
          (RelLanguage.rootU L U hU ⟨F.1, h⟩
            (RelLanguage.appendU L U hU F x y))
     else False) ↔ _
  simp [F.2]

end Structure
end StructuralRamsey

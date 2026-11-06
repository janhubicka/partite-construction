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
  rel R x := by
    classical
    exact if hr : R ∈ U then
      let F : U := ⟨R, hr⟩
      RelLanguage.lastU L U hU F x ∈
        C.func F (RelLanguage.rootU L U hU F x)
    else
      C.rel ⟨R, hr⟩ x

/-- Direct membership presentation of a decoded distinguished relation;
the subtype witnesses are proof-irrelevant. -/
@[simp] theorem toRelU_func_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V)
    (F : U) (t : Fin (L.arity F.1) → V) :
    (toRelU U hU C).rel F.1 t ↔
      RelLanguage.lastU L U hU F t ∈
        C.func F (RelLanguage.rootU L U hU F t) := by
  classical
  simpa only [toRelU, dif_pos F.2]

/-- The non-U relations are left unchanged by arbitrary-target decoding. -/
@[simp] theorem toRelU_rel_not_mem_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V)
    (R : L.Symbol) (hR : R ∉ U) (t : Fin (L.arity R) → V) :
    (toRelU U hU C).rel R t ↔ C.rel ⟨R, hR⟩ t := by
  classical
  simpa only [toRelU, dif_neg hR]

end Structure

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v}

theorem toRelU_asUFunctionsReduced_rel_iff
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (R : L.Symbol) (x : Fin (L.arity R) → V) :
    (Structure.toRelU U hU (A.asUFunctionsReduced U hU)).rel R x ↔
      A.rel R x := by
  classical
  by_cases h : R ∈ U
  · simp [Structure.toRelU, RelStructure.asUFunctionsReduced, h,
      RelLanguage.appendU_root_last]
  · simp [Structure.toRelU, RelStructure.asUFunctionsReduced, h]

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
  classical
  change (Structure.toRelU U hU C).rel R.1 x ↔ C.rel R x
  have hnot : R.1 ∉ U := R.2
  have hid : C.rel ⟨R.1, hnot⟩ x ↔ C.rel R x := Iff.rfl
  simpa only [Structure.toRelU, dif_neg hnot] using hid

theorem asUFunctionsReduced_toRelU_func_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) V)
    (F : (L.withUFunctionsReduced U).FuncSymbol)
    (x : Fin ((L.withUFunctionsReduced U).funcArity F) → V)
    (y : V) :
    y ∈ (RelStructure.asUFunctionsReduced (toRelU U hU C) U hU).func F x ↔
      y ∈ C.func F x := by
  change (Structure.toRelU U hU C).rel F.1
    (RelLanguage.appendU L U hU F x y) ↔ y ∈ C.func F x
  simpa only [Structure.toRelU_func_iff,
    RelLanguage.rootU_append, RelLanguage.lastU_append]

end Structure

namespace RelLanguage

@[simp] theorem rootU_comp
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v} {W : Type w}
    (f : V → W) (t : Fin (L.arity F.1) → V) :
    rootU L U hU F (f ∘ t) = f ∘ rootU L U hU F t := rfl

@[simp] theorem lastU_comp
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v} {W : Type w}
    (f : V → W) (t : Fin (L.arity F.1) → V) :
    lastU L U hU F (f ∘ t) = f (lastU L U hU F t) := rfl

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- No U relation is duplicated: a U-closed induced relational embedding
is a full embedding in the REDUCED mixed signature, on the same map. -/
def Embedding.toReducedUFunctions
    {A : RelStructure L V} {B : RelStructure L W}
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B) (he : IsUClosedEmbedding A B U hU e) :
    Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R.1 x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hh : B.rel F.1
          (e ∘ RelLanguage.appendU L U hU F x z) :=
        (e.map_rel_iff F.1 (RelLanguage.appendU L U hU F x z)).mpr hz
      have hcomp := RelLanguage.appendU_comp L U hU F e.toFun x z
      exact Eq.mp (congrArg (B.rel F.1) hcomp) hh
    · intro hy
      exact he F x y hy

end RelStructure

namespace Structure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- A full embedding maps a specific source function value to an arbitrary
target value iff the target value is the image of that very source value. -/
theorem Embedding.func_mem_map_iff
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {C : Structure (L.withUFunctionsReduced U) V}
    {D : Structure (L.withUFunctionsReduced U) W}
    (f : Embedding C D)
    (F : (L.withUFunctionsReduced U).FuncSymbol)
    (x : Fin ((L.withUFunctionsReduced U).funcArity F) → V)
    (y : V) :
    f y ∈ D.func F (f ∘ x) ↔ y ∈ C.func F x := by
  rw [← f.map_func F x]
  constructor
  · rintro ⟨z, hz, heq⟩
    have he : z = y := f.injective heq
    simpa [he] using hz
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The nonredundant decoder converts ANY full functional embedding into
an induced relational embedding, including the formerly U-relations. -/
def Embedding.toRelU
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {C : Structure (L.withUFunctionsReduced U) V}
    {D : Structure (L.withUFunctionsReduced U) W}
    (f : Embedding C D) :
    RelStructure.Embedding (Structure.toRelU U hU C)
      (Structure.toRelU U hU D) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    by_cases hR : R ∈ U
    · let F : U := ⟨R, hR⟩
      have hm := f.func_mem_map_iff U hU F
        (RelLanguage.rootU L U hU F x)
        (RelLanguage.lastU L U hU F x)
      have hh : (Structure.toRelU U hU D).rel R (f.toFun ∘ x) ↔
          f (RelLanguage.lastU L U hU F x) ∈
            D.func F (f.toFun ∘ RelLanguage.rootU L U hU F x) := by
        simpa only [F, Structure.toRelU_func_iff,
          RelLanguage.rootU_comp, RelLanguage.lastU_comp]
      have hc : (Structure.toRelU U hU C).rel R x ↔
          RelLanguage.lastU L U hU F x ∈
            C.func F (RelLanguage.rootU L U hU F x) :=
        Structure.toRelU_func_iff U hU C F x
      exact hh.trans (hm.trans hc.symm)
    · exact (Structure.toRelU_rel_not_mem_iff U hU D R hR (f.toFun ∘ x)).trans
        ((f.map_rel_iff ⟨R, hR⟩ x).trans
          (Structure.toRelU_rel_not_mem_iff U hU C R hR x).symm)

/-- A full map of arbitrary reduced functional witnesses has U-closed
relational range, without requiring redundant-symbol coherence. -/
theorem Embedding.toRelU_uClosed
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {C : Structure (L.withUFunctionsReduced U) V}
    {D : Structure (L.withUFunctionsReduced U) W}
    (f : Embedding C D) :
    RelStructure.IsUClosedEmbedding (Structure.toRelU U hU C)
      (Structure.toRelU U hU D) U hU (f.toRelU U hU) := by
  intro F x y hy
  have hf : y ∈ D.func F (f ∘ x) := by
    have ht := (Structure.toRelU_func_iff U hU D F
      (RelLanguage.appendU L U hU F (f.toFun ∘ x) y)).mp hy
    simpa only [RelLanguage.rootU_append, RelLanguage.lastU_append]
      using ht
  rw [← f.map_func F x] at hf
  rcases hf with ⟨z, hz, heq⟩
  refine ⟨z, ?_, heq⟩
  apply (Structure.toRelU_func_iff U hU C F
    (RelLanguage.appendU L U hU F x z)).mpr
  simpa only [RelLanguage.rootU_append, RelLanguage.lastU_append]
    using hz

end Structure
end StructuralRamsey

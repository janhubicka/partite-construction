import PartiteConstruction.Structure.NullaryRoot
import PartiteConstruction.Structure.Order
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false

/-! # Rooted reduction of nullary functions

The moving-part language records all incidences with a fixed finite root.
Every function symbol in the reduced language has positive arity.  This file
builds the reduction used to eliminate nullary functions from the ordered
functional EHN theorem.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v w

/-- A pattern says which input coordinates are occupied by fixed root
vertices.  Coordinates carrying `none` remain moving variables. -/
structure Pattern (n : ℕ) (R : Type v) where
  fixed : Fin n → Option R

namespace Pattern

universe u
variable {n : ℕ} {R : Type v}

def Move (p : Pattern n R) := {i : Fin n // p.fixed i = none}

noncomputable def moveFintype (p : Pattern n R) : Fintype p.Move := by
  letI : Finite p.Move :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite p.Move

noncomputable def arity (p : Pattern n R) : ℕ :=
  @Fintype.card p.Move p.moveFintype

noncomputable def moveEquiv (p : Pattern n R) :
    p.Move ≃ Fin p.arity :=
  @Fintype.equivFin p.Move p.moveFintype

theorem arity_pos_of_moving (p : Pattern n R) {i : Fin n}
    (hi : p.fixed i = none) : 0 < p.arity := by
  classical
  letI : Fintype p.Move := p.moveFintype
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- Fill a rooted pattern by a tuple of moving vertices. -/
noncomputable def fill
    {L : Language.{u}} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (p : Pattern n R)
    (x : Fin p.arity → {a : U // a ∉ Set.range ρ}) :
    Fin n → U :=
  fun i =>
    match h : p.fixed i with
    | some r => ρ r
    | none => (x (p.moveEquiv ⟨i, h⟩)).1


/-- Pattern induced by a tuple in a disjoint union of the fixed root and the
moving carrier. -/
def ofTuple {V : Type w} (t : Fin n → Sum R V) : Pattern n R where
  fixed i :=
    match t i with
    | .inl r => some r
    | .inr _ => none

/-- Value of a moving coordinate of a tuple. -/
noncomputable def moveValue {V : Type w} (t : Fin n → Sum R V)
    (i : (ofTuple t).Move) : V :=
  match h : t i.1 with
  | .inl r =>
      False.elim (by
        have hi := i.2
        simp [ofTuple, h] at hi)
  | .inr x => x

/-- Canonical moving tuple, indexed by the arity of the induced pattern. -/
noncomputable def movingTuple {V : Type w} (t : Fin n → Sum R V) :
    Fin (ofTuple t).arity → V :=
  fun j => moveValue t ((ofTuple t).moveEquiv.symm j)

/-- Reassemble a sum tuple from a root pattern and its moving coordinates. -/
noncomputable def sumFill {V : Type w} (p : Pattern n R)
    (x : Fin p.arity → V) : Fin n → Sum R V :=
  fun i =>
    match h : p.fixed i with
    | some r => Sum.inl r
    | none => Sum.inr (x (p.moveEquiv ⟨i, h⟩))

@[simp] theorem sumFill_ofTuple_movingTuple {V : Type w}
    (t : Fin n → Sum R V) :
    sumFill (ofTuple t) (movingTuple t) = t := by
  funext i
  cases h : t i with
  | inl r =>
      simp [sumFill, ofTuple, h]
  | inr x =>
      simp [sumFill, ofTuple, movingTuple, moveValue, h]

def HasMoving {V : Type w} (t : Fin n → Sum R V) : Prop :=
  ∃ i v, t i = Sum.inr v

theorem arity_pos_of_hasMoving {V : Type w} (t : Fin n → Sum R V)
    (h : HasMoving t) : 0 < (ofTuple t).arity := by
  obtain ⟨i, v, hi⟩ := h
  apply arity_pos_of_moving (ofTuple t) (i := i)
  simp [ofTuple, hi]

/-- When a tuple has no moving coordinate, read it as a root tuple. -/
noncomputable def rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬ HasMoving t) : Fin n → R :=
  fun i =>
    match hi : t i with
    | .inl r => r
    | .inr v => False.elim (h ⟨i, v, hi⟩)

@[simp] theorem inl_rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬ HasMoving t) :
    Sum.inl ∘ rootTuple t h = t := by
  funext i
  cases hi : t i with
  | inl r => simp [rootTuple, hi]
  | inr v => exact False.elim (h ⟨i, v, hi⟩)

end Pattern

/-- Vertices outside a fixed embedded root. -/
def Outside
    {L : Language.{u}} {R : Type v} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :=
  {a : U // a ∉ Set.range ρ}

/-- Relation symbols of the moving language.  Root-only facts are supplied by
the fixed root itself and therefore are not named here. -/
inductive RelSymbol (L : Language.{u}) (R : Type v) : Type (max u v)
  | base (S : L.RelSymbol) (p : Pattern (L.relArity S) R)
      (moving : 0 < p.arity)
  | output (F : L.FuncSymbol) (p : Pattern (L.funcArity F) R)
      (moving : 0 < p.arity) (r : R)
  | cut (r : R)

/-- Function symbols retain exactly those applications having at least one
moving input.  Outputs in the root are represented by `RelSymbol.output`. -/
structure FuncSymbol (L : Language.{u}) (R : Type v) : Type (max u v) where
  F : L.FuncSymbol
  p : Pattern (L.funcArity F) R
  moving : 0 < p.arity

/-- The rooted moving-part language.  Its function symbols all have positive
input arity, irrespective of nullary functions in the original language. -/
noncomputable def language (L : Language.{u}) (R : Type v) :
    Language.{max u v} where
  RelSymbol := RelSymbol L R
  FuncSymbol := FuncSymbol L R
  relArity
    | .base _ p _ => p.arity
    | .output _ p _ _ => p.arity
    | .cut _ => 1
  funcArity q := q.p.arity

theorem language_positive
    (L : Language.{u}) (R : Type v) :
    (language L R).PositiveFuncArity := by
  intro q
  exact q.moving

/-- Reconstruct an original-language structure by adjoining the fixed root.
Root-only facts come from `Root`; all incidences meeting the moving carrier
are read from the rooted language. -/
noncomputable def decode
    {L : Language.{u}} {R : Type v} {V : Type w}
    (Root : Structure L R) (C : Structure (language L R) V) :
    Structure L (Sum R V) where
  rel S t :=
    if h : Pattern.HasMoving t then
      C.rel
        (.base S (Pattern.ofTuple t)
          (Pattern.arity_pos_of_hasMoving t h))
        (Pattern.movingTuple t)
    else
      Root.rel S (Pattern.rootTuple t h)
  func F t :=
    {y |
      if h : Pattern.HasMoving t then
        match y with
        | .inl r =>
            C.rel
              (.output F (Pattern.ofTuple t)
                (Pattern.arity_pos_of_hasMoving t h) r)
              (Pattern.movingTuple t)
        | .inr z =>
            z ∈ C.func
              ⟨F, Pattern.ofTuple t,
                Pattern.arity_pos_of_hasMoving t h⟩
              (Pattern.movingTuple t)
      else
        match y with
        | .inl r => r ∈ Root.func F (Pattern.rootTuple t h)
        | .inr _ => False}

/-- Extend a map of moving carriers by the identity on the fixed root. -/
def sumMap {R : Type v} {V W : Type w} (f : V → W) :
    Sum R V → Sum R W
  | .inl r => .inl r
  | .inr x => .inr (f x)

theorem sumMap_injective {R : Type v} {V W : Type w}
    {f : V → W} (hf : Function.Injective f) :
    Function.Injective (sumMap (R := R) f) := by
  intro x y h
  cases x <;> cases y <;> simp [sumMap] at h ⊢
  exact hf h

/-- Encode a rooted ordered structure on the complement of the root. -/
noncomputable def encode
    {L : Language.{u}} {R : Type v} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A) :
    Structure (language L R) (Outside ρ) where
  rel Q x :=
    match Q with
    | .base S p _ => A.rel S (p.fill ρ x)
    | .output F p _ r => ρ r ∈ A.func F (p.fill ρ x)
    | .cut r => ρ r < (x ⟨0, by simp [language]⟩).1
  func Q x := {y | y.1 ∈ A.func Q.F (Q.p.fill ρ x)}

end StructuralRamsey.Rooted

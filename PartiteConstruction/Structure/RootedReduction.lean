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

variable {n : ℕ} {R : Type v}

def Move (p : Pattern n R) := {i : Fin n // p.fixed i = none}

noncomputable def moveFintype (p : Pattern n R) : Fintype p.Move :=
  Fintype.ofFinite p.Move

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
    {U : Type w} {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (p : Pattern n R)
    (x : Fin p.arity → {a : U // a ∉ Set.range ρ}) :
    Fin n → U :=
  fun i =>
    match h : p.fixed i with
    | some r => ρ r
    | none => (x (p.moveEquiv ⟨i, h⟩)).1

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
    | .cut r => ρ r < (x 0).1
  func Q x := {y | y.1 ∈ A.func Q.F (Q.p.fill ρ x)}

end StructuralRamsey.Rooted

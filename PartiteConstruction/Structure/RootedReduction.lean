import PartiteConstruction.Structure.NullaryRoot
import PartiteConstruction.Structure.Order
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false

/-! # Rooted reduction of nullary functions

Fix a finite root.  The moving language records all incidences meeting the
moving carrier.  Root coordinates are named in the symbol and ignored in the
moving tuple.  Function symbols get one additional dummy coordinate, hence
have positive arity even when the original function is nullary.

The dummy is chosen canonically from the first moving input.  Thus the
encoding is functorial without quotienting tuples or carrying dependent arity
casts.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v w
variable {n : ℕ}

/-- A rooted input pattern: `some r` fixes that coordinate to the root
vertex r; `none` leaves it moving. -/
structure Pattern (n : ℕ) (R : Type v) where
  fixed : Fin n → Option R

namespace Pattern

variable {R : Type v}

@[ext] theorem ext {p q : Pattern n R} (h : p.fixed = q.fixed) : p = q := by
  cases p
  cases q
  simp_all

def HasMoving (p : Pattern n R) : Prop :=
  ∃ i, p.fixed i = none

noncomputable def firstMoving (p : Pattern n R) (h : p.HasMoving) : Fin n :=
  Classical.choose h

theorem firstMoving_spec (p : Pattern n R) (h : p.HasMoving) :
    p.fixed (p.firstMoving h) = none :=
  Classical.choose_spec h

/-- Pattern induced by a tuple in the disjoint union of root and moving
vertices. -/
def ofTuple {V : Type w} (t : Fin n → Sum R V) : Pattern n R where
  fixed i :=
    match t i with
    | .inl r => some r
    | .inr _ => none

theorem ofTuple_hasMoving_iff {V : Type w} (t : Fin n → Sum R V) :
    (ofTuple t).HasMoving ↔ ∃ i v, t i = Sum.inr v := by
  constructor
  · rintro ⟨i, hi⟩
    cases hti : t i with
    | inl r =>
        simp [ofTuple, hti] at hi
    | inr v =>
        exact ⟨i, v, hti⟩
  · rintro ⟨i, v, hi⟩
    exact ⟨i, by simp [ofTuple, hi]⟩

/-- A moving coordinate known from its rooted pattern. -/
noncomputable def moveAt {V : Type w} (t : Fin n → Sum R V)
    (i : Fin n) (hi : (ofTuple t).fixed i = none) : V :=
  match h : t i with
  | .inl r =>
      False.elim (by
        have := hi
        simp [ofTuple, h] at this)
  | .inr x => x

/-- Canonical dummy moving vertex: the value at the first moving input. -/
noncomputable def dummy {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) : V :=
  moveAt t ((ofTuple t).firstMoving h)
    ((ofTuple t).firstMoving_spec h)

/-- Replace every fixed-root position by the canonical dummy, leaving moving
coordinates unchanged. -/
noncomputable def pad {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) : Fin n → V :=
  fun i =>
    match hi : t i with
    | .inl _ => dummy t h
    | .inr x => x

/-- Fill a rooted pattern in an original structure.  Values of x at fixed
coordinates are ignored. -/
def fill
    {L : Language.{u}} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) (p : Pattern n R)
    (x : Fin n → {a : U // a ∉ Set.range ρ}) :
    Fin n → U :=
  fun i =>
    match p.fixed i with
    | some r => ρ r
    | none => (x i).1

/-- Fill a rooted pattern in a disjoint union. -/
def sumFill {V : Type w} (p : Pattern n R)
    (x : Fin n → V) : Fin n → Sum R V :=
  fun i =>
    match p.fixed i with
    | some r => Sum.inl r
    | none => Sum.inr (x i)

@[simp] theorem ofTuple_sumFill {V : Type w}
    (p : Pattern n R) (x : Fin n → V) :
    ofTuple (sumFill p x) = p := by
  apply Pattern.ext
  funext i
  cases h : p.fixed i with
  | some r => simp [ofTuple, sumFill, h]
  | none => simp [ofTuple, sumFill, h]

@[simp] theorem sumFill_ofTuple_pad {V : Type w}
    (t : Fin n → Sum R V) (h : (ofTuple t).HasMoving) :
    sumFill (ofTuple t) (pad t h) = t := by
  funext i
  cases hi : t i with
  | inl r => simp [sumFill, ofTuple, pad, hi]
  | inr x => simp [sumFill, ofTuple, pad, hi]

/-- When there is no moving coordinate, read the tuple in the root. -/
noncomputable def rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) : Fin n → R :=
  fun i =>
    match hi : t i with
    | .inl r => r
    | .inr v =>
        False.elim (h ((ofTuple_hasMoving_iff t).2 ⟨i, v, hi⟩))

@[simp] theorem inl_rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) :
    Sum.inl ∘ rootTuple t h = t := by
  funext i
  cases hi : t i with
  | inl r => simp [rootTuple, hi]
  | inr v =>
      exact False.elim (h ((ofTuple_hasMoving_iff t).2 ⟨i, v, hi⟩))

theorem rootTuple_inl {V : Type w} (x : Fin n → R)
    (h : ¬(ofTuple (Sum.inl ∘ x : Fin n → Sum R V)).HasMoving) :
    rootTuple (Sum.inl ∘ x : Fin n → Sum R V) h = x := by
  funext i
  have hi := congrFun
    (inl_rootTuple (Sum.inl ∘ x : Fin n → Sum R V) h) i
  exact Sum.inl.inj hi

end Pattern

/-- Vertices outside a fixed embedded root. -/
def Outside
    {L : Language.{u}} {R : Type v} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    (ρ : Structure.Embedding Root A) :=
  {a : U // a ∉ Set.range ρ}

/-- Relation symbols on the moving part.  Root-only facts are supplied by the
fixed root.  Function outputs landing in the root are relations. -/
inductive RelSymbol (L : Language.{u}) (R : Type v) : Type (max u v)
  | base (S : L.RelSymbol) (p : Pattern (L.relArity S) R)
  | output (F : L.FuncSymbol) (p : Pattern (L.funcArity F) R) (r : R)
  | cut (r : R)

/-- Moving function outputs.  The additional final coordinate is a dummy, so
all reduced function symbols have positive arity. -/
structure FuncSymbol (L : Language.{u}) (R : Type v) : Type (max u v) where
  F : L.FuncSymbol
  p : Pattern (L.funcArity F) R

def language (L : Language.{u}) (R : Type v) :
    Language.{max u v} where
  RelSymbol := RelSymbol L R
  FuncSymbol := FuncSymbol L R
  relArity
    | .base S _ => L.relArity S
    | .output F _ _ => L.funcArity F
    | .cut _ => 1
  funcArity q := L.funcArity q.F + 1

theorem language_positive (L : Language.{u}) (R : Type v) :
    (language L R).PositiveFuncArity := by
  intro q
  exact Nat.zero_lt_succ _

/-- Extend a moving map by the identity on the root. -/
def sumMap {R : Type v} {V W : Type w} (f : V → W) :
    Sum R V → Sum R W
  | .inl r => .inl r
  | .inr x => .inr (f x)

theorem sumMap_injective {R : Type v} {V W : Type w}
    {f : V → W} (hf : Function.Injective f) :
    Function.Injective (sumMap (R := R) f) := by
  intro x y h
  cases x with
  | inl r =>
      cases y with
      | inl s => exact Sum.inl.inj h
      | inr y => cases h
  | inr x =>
      cases y with
      | inl s => cases h
      | inr y =>
          apply congrArg Sum.inr
          exact hf (Sum.inr.inj h)

theorem Pattern.ofTuple_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V) :
    Pattern.ofTuple (sumMap f ∘ t) = Pattern.ofTuple t := by
  apply Pattern.ext
  funext i
  cases h : t i <;> simp [Pattern.ofTuple, sumMap, h]

theorem Pattern.hasMoving_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V) :
    (Pattern.ofTuple (sumMap f ∘ t)).HasMoving ↔
      (Pattern.ofTuple t).HasMoving := by
  rw [Pattern.ofTuple_sumMap]

theorem Pattern.dummy_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : (Pattern.ofTuple t).HasMoving)
    (h' : (Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.dummy (sumMap f ∘ t) h' = f (Pattern.dummy t h) := by
  have hp := Pattern.ofTuple_sumMap f t
  cases hp
  unfold Pattern.dummy Pattern.moveAt
  simp only [Function.comp_apply, sumMap]
  split
  · rename_i r hr
    have hs := (Pattern.ofTuple t).firstMoving_spec h
    simp [Pattern.ofTuple, hr] at hs
  · rfl

theorem Pattern.pad_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : (Pattern.ofTuple t).HasMoving)
    (h' : (Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.pad (sumMap f ∘ t) h' =
      f ∘ Pattern.pad t h := by
  funext i
  cases hi : t i with
  | inl r =>
      simp [Pattern.pad, hi, sumMap,
        Pattern.dummy_sumMap f t h h']
  | inr x =>
      simp [Pattern.pad, hi, sumMap]

theorem Pattern.rootTuple_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : ¬(Pattern.ofTuple t).HasMoving)
    (h' : ¬(Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.rootTuple (sumMap f ∘ t) h' =
      Pattern.rootTuple t h := by
  funext i
  cases hi : t i with
  | inl r => simp [Pattern.rootTuple, sumMap, hi]
  | inr x =>
      exact False.elim
        (h ((Pattern.ofTuple_hasMoving_iff t).2 ⟨i, x, hi⟩))

/-- Reconstruct an original-language structure by adjoining the fixed root. -/
noncomputable def decode
    {L : Language.{u}} {R : Type v} {V : Type w}
    (Root : Structure L R) (C : Structure (language L R) V) :
    Structure L (Sum R V) := by
  classical
  exact {
    rel := fun S t =>
      if h : (Pattern.ofTuple t).HasMoving then
        C.rel (.base S (Pattern.ofTuple t)) (Pattern.pad t h)
      else
        Root.rel S (Pattern.rootTuple t h)
    func := fun F t =>
      {y |
        if h : (Pattern.ofTuple t).HasMoving then
          match y with
          | .inl r =>
              C.rel (.output F (Pattern.ofTuple t) r) (Pattern.pad t h)
          | .inr z =>
              z ∈ C.func ⟨F, Pattern.ofTuple t⟩
                (Structure.funcTuple (Pattern.pad t h) (Pattern.dummy t h))
        else
          match y with
          | .inl r => r ∈ Root.func F (Pattern.rootTuple t h)
          | .inr _ => False}
  }

/-- Encode a rooted ordered structure on the complement of the root. -/
def encode
    {L : Language.{u}} {R : Type v} {U : Type w}
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A) :
    Structure (language L R) (Outside ρ) where
  rel Q x :=
    match Q with
    | .base S p => A.rel S (p.fill ρ x)
    | .output F p r => ρ r ∈ A.func F (p.fill ρ x)
    | .cut r => ρ r < (x 0).1
  func Q x :=
    {y |
      y.1 ∈ A.func Q.F
        (Q.p.fill ρ (fun i => x i.castSucc))}

end StructuralRamsey.Rooted

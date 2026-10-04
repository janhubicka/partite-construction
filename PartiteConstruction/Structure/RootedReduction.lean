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

/-- A coordinate declared moving by the pattern really is a moving
vertex. -/
theorem exists_moveAt {V : Type w} (t : Fin n → Sum R V)
    (i : Fin n) (hi : (ofTuple t).fixed i = none) :
    ∃ x : V, t i = Sum.inr x := by
  cases hti : t i with
  | inl r =>
      have : (ofTuple t).fixed i = some r := by
        simp [ofTuple, hti]
      rw [this] at hi
      contradiction
  | inr x => exact ⟨x, rfl⟩

/-- A moving coordinate known from its rooted pattern. -/
noncomputable def moveAt {V : Type w} (t : Fin n → Sum R V)
    (i : Fin n) (hi : (ofTuple t).fixed i = none) : V :=
  Classical.choose (exists_moveAt t i hi)

theorem moveAt_spec {V : Type w} (t : Fin n → Sum R V)
    (i : Fin n) (hi : (ofTuple t).fixed i = none) :
    t i = Sum.inr (moveAt t i hi) :=
  Classical.choose_spec (exists_moveAt t i hi)

/-- Canonical dummy moving vertex: the value at the first moving input. -/
noncomputable def dummy {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) : V :=
  moveAt t ((ofTuple t).firstMoving h)
    ((ofTuple t).firstMoving_spec h)

theorem dummy_spec {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) :
    t ((ofTuple t).firstMoving h) = Sum.inr (dummy t h) :=
  moveAt_spec t _ _

/-- Replace every fixed-root position by the canonical dummy, leaving moving
coordinates unchanged. -/
noncomputable def pad {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) : Fin n → V :=
  fun i =>
    if hi : (ofTuple t).fixed i = none then moveAt t i hi else dummy t h

theorem pad_eq_moveAt {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) (i : Fin n)
    (hi : (ofTuple t).fixed i = none) :
    pad t h i = moveAt t i hi := by
  simp [pad, hi]

theorem pad_eq_dummy {V : Type w} (t : Fin n → Sum R V)
    (h : (ofTuple t).HasMoving) (i : Fin n)
    (hi : (ofTuple t).fixed i ≠ none) :
    pad t h i = dummy t h := by
  simp [pad, hi]

/-- Canonicalize a tuple by replacing fixed-root coordinates by the
value at the first moving coordinate. -/
noncomputable def normalize {V : Type w}
    (p : Pattern n R) (h : p.HasMoving) (x : Fin n → V) :
    Fin n → V :=
  fun i => if hi : p.fixed i = none then x i else x (p.firstMoving h)

theorem normalize_eq_self_of_comp
    {V W : Type w} (p : Pattern n R) (h : p.HasMoving)
    (e : V → W) (he : Function.Injective e)
    (y : Fin n → W) (x : Fin n → V)
    (hy : normalize p h y = e ∘ x) :
    normalize p h x = x := by
  funext i
  by_cases hi : p.fixed i = none
  · simp [normalize, hi]
  · have hj : p.fixed (p.firstMoving h) = none := p.firstMoving_spec h
    have hiEq := congrFun hy i
    have hjEq := congrFun hy (p.firstMoving h)
    have hex : e (x i) = e (x (p.firstMoving h)) := by
      rw [← hiEq, ← hjEq]
      simp [normalize, hi, hj]
    have hxi : x i = x (p.firstMoving h) := he hex
    simp [normalize, hi, hxi]

theorem normalize_pad {V : Type w}
    (t : Fin n → Sum R V) (h : (ofTuple t).HasMoving) :
    normalize (ofTuple t) h (pad t h) = pad t h := by
  funext i
  by_cases hi : (ofTuple t).fixed i = none
  · simp [normalize, hi]
  · have hj := (ofTuple t).firstMoving_spec h
    have hfirst :
        pad t h ((ofTuple t).firstMoving h) = dummy t h := by
      rw [pad_eq_moveAt _ h _ hj]
      rfl
    rw [normalize]
    simp only [hi, ↓reduceDIte]
    rw [hfirst, pad_eq_dummy _ h i hi]

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
  | inl r =>
      have hfix : (ofTuple t).fixed i = some r := by
        simp [ofTuple, hi]
      simp only [sumFill, hfix]
  | inr x =>
      have hfix : (ofTuple t).fixed i = none := by
        simp [ofTuple, hi]
      simp only [sumFill, hfix]
      have hs := moveAt_spec t i hfix
      rw [hi] at hs
      apply congrArg Sum.inr
      calc
        pad t h i = moveAt t i hfix := pad_eq_moveAt t h i hfix
        _ = x := (Sum.inr.inj hs).symm

/-- Padding a tuple reconstructed from a pattern is exactly normalization. -/
theorem pad_sumFill {V : Type w}
    (p : Pattern n R) (h : p.HasMoving) (x : Fin n → V) :
    let t := sumFill p x
    let ht : (ofTuple t).HasMoving := by
      rw [ofTuple_sumFill]
      exact h
    pad t ht = normalize p h x := by
  dsimp only
  funext i
  by_cases hi : p.fixed i = none
  · have hfix : (ofTuple (sumFill p x)).fixed i = none := by
      rw [ofTuple_sumFill]
      exact hi
    rw [pad_eq_moveAt _ _ i hfix]
    have hs := moveAt_spec (sumFill p x) i hfix
    simp only [sumFill, hi] at hs
    exact (Sum.inr.inj hs).symm
  · have hfix : (ofTuple (sumFill p x)).fixed i ≠ none := by
      rw [ofTuple_sumFill]
      exact hi
    rw [pad_eq_dummy _ _ i hfix]
    have hp : ofTuple (sumFill p x) = p := ofTuple_sumFill p x
    have hm :
        (ofTuple (sumFill p x)).firstMoving
            (by rw [hp]; exact h) =
          p.firstMoving h :=
      firstMoving_congr hp (by rw [hp]; exact h) h
    unfold dummy
    rw [hm]
    have hj := p.firstMoving_spec h
    have hj' : (ofTuple (sumFill p x)).fixed (p.firstMoving h) = none := by
      rw [hp]
      exact hj
    have hs := moveAt_spec (sumFill p x) (p.firstMoving h) hj'
    simp only [sumFill, hj] at hs
    have hmove :
        moveAt (sumFill p x) (p.firstMoving h) hj' =
          x (p.firstMoving h) :=
      (Sum.inr.inj hs).symm
    simpa [normalize, hi] using hmove

theorem dummy_sumFill {V : Type w}
    (p : Pattern n R) (h : p.HasMoving) (x : Fin n → V) :
    let t := sumFill p x
    let ht : (ofTuple t).HasMoving := by
      rw [ofTuple_sumFill]
      exact h
    dummy t ht = x (p.firstMoving h) := by
  dsimp only
  have hp : ofTuple (sumFill p x) = p := ofTuple_sumFill p x
  have hm :
      (ofTuple (sumFill p x)).firstMoving
          (by rw [hp]; exact h) =
        p.firstMoving h :=
    firstMoving_congr hp (by rw [hp]; exact h) h
  unfold dummy
  rw [hm]
  have hj := p.firstMoving_spec h
  have hj' : (ofTuple (sumFill p x)).fixed (p.firstMoving h) = none := by
    rw [hp]
    exact hj
  have hs := moveAt_spec (sumFill p x) (p.firstMoving h) hj'
  simp only [sumFill, hj] at hs
  exact (Sum.inr.inj hs).symm

theorem funcTuple_preimage_canonical
    {V W : Type w} (e : V → W) (he : Function.Injective e)
    (t : Fin n → Sum R W) (h : (ofTuple t).HasMoving)
    (q : Fin (n + 1) → V)
    (heq :
      Structure.funcTuple (pad t h) (dummy t h) = e ∘ q) :
    let x : Fin n → V := fun i => q i.castSucc
    let a := sumFill (ofTuple t) x
    let ha : (ofTuple a).HasMoving := by
      rw [ofTuple_sumFill]
      exact h
    Structure.funcTuple (pad a ha) (dummy a ha) = q := by
  dsimp only
  let x : Fin n → V := fun i => q i.castSucc
  let a := sumFill (ofTuple t) x
  let ha : (ofTuple a).HasMoving := by
    rw [ofTuple_sumFill]
    exact h
  have hargs : pad t h = e ∘ x := by
    funext i
    have hi := congrFun heq i.castSucc
    simpa [x, Structure.funcTuple_castSucc] using hi
  have hnormTarget := normalize_pad t h
  have hnormX :
      normalize (ofTuple t) h x = x :=
    normalize_eq_self_of_comp (ofTuple t) h e he (pad t h) x
      (hnormTarget.trans hargs)
  have hpad : pad a ha = x := by
    have hp := pad_sumFill (ofTuple t) h x
    dsimp only at hp
    exact hp.trans hnormX
  have hlast := congrFun heq (Fin.last n)
  have htargetLast :
      dummy t h = e (q (Fin.last n)) := by
    simpa [Structure.funcTuple_last] using hlast
  have j := (ofTuple t).firstMoving h
  have hj := (ofTuple t).firstMoving_spec h
  have hpadj : pad t h j = dummy t h := by
    rw [pad_eq_moveAt _ h j hj]
    rfl
  have hargj := congrFun hargs j
  have hxlast : x j = q (Fin.last n) := by
    apply he
    rw [← hargj, hpadj, htargetLast]
  have hdummy : dummy a ha = q (Fin.last n) := by
    have hd := dummy_sumFill (ofTuple t) h x
    dsimp only at hd
    exact hd.trans hxlast
  apply Structure.funcTuple_eta q ▸ ?_
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [hpad, hdummy, Structure.funcTuple_last]
  · simp [hpad, x, Structure.funcTuple_castSucc]

/-- A tuple with no moving coordinates consists entirely of root vertices. -/
theorem exists_rootAt {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) (i : Fin n) :
    ∃ r : R, t i = Sum.inl r := by
  cases hi : t i with
  | inl r => exact ⟨r, rfl⟩
  | inr v =>
      exact False.elim (h ((ofTuple_hasMoving_iff t).2 ⟨i, v, hi⟩))

/-- When there is no moving coordinate, read the tuple in the root. -/
noncomputable def rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) : Fin n → R :=
  fun i => Classical.choose (exists_rootAt t h i)

theorem rootTuple_spec {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) (i : Fin n) :
    t i = Sum.inl (rootTuple t h i) :=
  Classical.choose_spec (exists_rootAt t h i)

@[simp] theorem inl_rootTuple {V : Type w} (t : Fin n → Sum R V)
    (h : ¬(ofTuple t).HasMoving) :
    Sum.inl ∘ rootTuple t h = t := by
  funext i
  exact (rootTuple_spec t h i).symm

theorem rootTuple_inl {V : Type w} (x : Fin n → R)
    (h : ¬(ofTuple (Sum.inl ∘ x : Fin n → Sum R V)).HasMoving) :
    rootTuple (Sum.inl ∘ x : Fin n → Sum R V) h = x := by
  funext i
  have hi := congrFun
    (inl_rootTuple (Sum.inl ∘ x : Fin n → Sum R V) h) i
  exact Sum.inl.inj hi

end Pattern

/-- Vertices outside a fixed embedded root. -/
abbrev Outside
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

abbrev language (L : Language.{u}) (R : Type v) :
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

theorem Pattern.sumMap_sumFill_of_pad_eq
    {R : Type v} {V W : Type w} (e : V → W)
    (t : Fin n → Sum R W) (h : (Pattern.ofTuple t).HasMoving)
    (x : Fin n → V)
    (heq : Pattern.pad t h = e ∘ x) :
    sumMap e ∘ Pattern.sumFill (Pattern.ofTuple t) x = t := by
  funext i
  cases ht : t i with
  | inl r =>
      have hp : (Pattern.ofTuple t).fixed i = some r := by
        simp [Pattern.ofTuple, ht]
      simp [Pattern.sumFill, sumMap, hp, ht]
  | inr y =>
      have hp : (Pattern.ofTuple t).fixed i = none := by
        simp [Pattern.ofTuple, ht]
      have hm := Pattern.moveAt_spec t i hp
      rw [ht] at hm
      have hpad : Pattern.pad t h i = y := by
        rw [Pattern.pad_eq_moveAt _ h i hp]
        exact (Sum.inr.inj hm).symm
      have hei := congrFun heq i
      have exy : e (x i) = y := hei.symm.trans hpad
      simp [Pattern.sumFill, sumMap, hp, ht, exy]

theorem sumMap_injective {R : Type v} {V W : Type w}
    {f : V → W} (hf : Function.Injective f) :
    Function.Injective (sumMap (R := R) f) := by
  intro x y h
  cases x with
  | inl r =>
      cases y with
      | inl s =>
          change Sum.inl r = Sum.inl s at h
          exact congrArg (fun z : R => (Sum.inl z : Sum R V))
            (Sum.inl.inj h)
      | inr y =>
          change Sum.inl r = Sum.inr (f y) at h
          cases h
  | inr x =>
      cases y with
      | inl s =>
          change Sum.inr (f x) = Sum.inl s at h
          cases h
      | inr y =>
          change Sum.inr (f x) = Sum.inr (f y) at h
          exact congrArg Sum.inr (hf (Sum.inr.inj h))

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

theorem Pattern.firstMoving_congr
    {R : Type v} {p q : Pattern n R}
    (hp : p = q) (h : p.HasMoving) (h' : q.HasMoving) :
    p.firstMoving h = q.firstMoving h' := by
  subst q
  have hh : h = h' := Subsingleton.elim _ _
  subst hh
  rfl

theorem Pattern.dummy_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : (Pattern.ofTuple t).HasMoving)
    (h' : (Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.dummy (sumMap f ∘ t) h' = f (Pattern.dummy t h) := by
  let p := Pattern.ofTuple t
  let q := Pattern.ofTuple (sumMap f ∘ t)
  have hpq : q = p := Pattern.ofTuple_sumMap f t
  have hi : q.firstMoving h' = p.firstMoving h :=
    Pattern.firstMoving_congr hpq h' h
  have hs := Pattern.dummy_spec t h
  have ht := Pattern.dummy_spec (sumMap f ∘ t) h'
  rw [hi] at ht
  have hmap :
      (sumMap f ∘ t) (p.firstMoving h) =
        Sum.inr (f (Pattern.dummy t h)) := by
    change sumMap f (t (p.firstMoving h)) =
      Sum.inr (f (Pattern.dummy t h))
    rw [hs]
    rfl
  rw [hmap] at ht
  exact (Sum.inr.inj ht).symm

theorem Pattern.moveAt_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V) (i : Fin n)
    (hi : (Pattern.ofTuple t).fixed i = none)
    (hi' : (Pattern.ofTuple (sumMap f ∘ t)).fixed i = none) :
    Pattern.moveAt (sumMap f ∘ t) i hi' =
      f (Pattern.moveAt t i hi) := by
  have hs := Pattern.moveAt_spec t i hi
  have ht := Pattern.moveAt_spec (sumMap f ∘ t) i hi'
  have hmap :
      (sumMap f ∘ t) i = Sum.inr (f (Pattern.moveAt t i hi)) := by
    change sumMap f (t i) = _
    rw [hs]
    rfl
  rw [hmap] at ht
  exact (Sum.inr.inj ht).symm

theorem Pattern.pad_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : (Pattern.ofTuple t).HasMoving)
    (h' : (Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.pad (sumMap f ∘ t) h' =
      f ∘ Pattern.pad t h := by
  funext i
  have hp := Pattern.ofTuple_sumMap f t
  by_cases hi : (Pattern.ofTuple t).fixed i = none
  · have hi' : (Pattern.ofTuple (sumMap f ∘ t)).fixed i = none := by
      rw [hp]
      exact hi
    change Pattern.pad (sumMap f ∘ t) h' i = f (Pattern.pad t h i)
    rw [Pattern.pad_eq_moveAt _ h' i hi',
      Pattern.pad_eq_moveAt _ h i hi]
    exact Pattern.moveAt_sumMap f t i hi hi'
  · have hi' : (Pattern.ofTuple (sumMap f ∘ t)).fixed i ≠ none := by
      rw [hp]
      exact hi
    change Pattern.pad (sumMap f ∘ t) h' i = f (Pattern.pad t h i)
    rw [Pattern.pad_eq_dummy _ h' i hi',
      Pattern.pad_eq_dummy _ h i hi]
    exact Pattern.dummy_sumMap f t h h'

theorem Pattern.rootTuple_sumMap
    {R : Type v} {V W : Type w} (f : V → W)
    (t : Fin n → Sum R V)
    (h : ¬(Pattern.ofTuple t).HasMoving)
    (h' : ¬(Pattern.ofTuple (sumMap f ∘ t)).HasMoving) :
    Pattern.rootTuple (sumMap f ∘ t) h' =
      Pattern.rootTuple t h := by
  funext i
  have hs := Pattern.rootTuple_spec t h i
  have ht := Pattern.rootTuple_spec (sumMap f ∘ t) h' i
  have hmap :
      (sumMap f ∘ t) i =
        Sum.inl (Pattern.rootTuple t h i) := by
    change sumMap f (t i) = _
    rw [hs]
    rfl
  rw [hmap] at ht
  exact (Sum.inl.inj ht).symm

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
    | .cut r => ρ r < (x ⟨0, by simp [language]⟩).1
  func Q x :=
    {y |
      y.1 ∈ A.func Q.F
        (Q.p.fill ρ (fun i => x i.castSucc))}

end StructuralRamsey.Rooted

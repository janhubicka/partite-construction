import PartiteConstruction.Ramsey.ClosureSingletonVacuity2019

/-! # Ordered paired equivalences: a persistent two-colouring

A is two consecutive matched pairs in different equivalence classes.
B is three consecutive matched pairs, with class pattern X,Y,X.
For every finite target whose E relation is an equivalence relation,
colour an A-embedding by the order of the two E-class labels. The first
and last A-subcopies of any B-copy receive opposite colours.

This proves the universal no-Ramsey-witness assertion on actual
RelStructure embeddings, not just a finite search. The closure-description
and strong-amalgamation bridges are separate from this module.
-/

namespace StructuralRamsey.RelStructure.PairedEquivalenceObstruction

open StructuralRamsey

inductive Symbol where
  | lt | equiv | mate
  deriving DecidableEq, Fintype

abbrev Lang : RelLanguage where
  Symbol := Symbol
  arity := fun _ => 2

abbrev edge {V : Type} (C : RelStructure Lang V) (R : Symbol)
    (x y : V) : Prop := C.rel R ![x, y]

/-- Finite members of this predicate form the candidate test class.
The order is arbitrary, not required to make E-classes convex. -/
structure IsPairedEquivalence {V : Type} (C : RelStructure Lang V) : Prop where
  lt_irrefl : ∀ x, ¬ edge C .lt x x
  lt_trans : ∀ x y z, edge C .lt x y → edge C .lt y z → edge C .lt x z
  lt_total : ∀ x y, x ≠ y → edge C .lt x y ∨ edge C .lt y x
  equiv : Equivalence (edge C .equiv)
  mate_irrefl : ∀ x, ¬ edge C .mate x x
  mate_symm : ∀ x y, edge C .mate x y → edge C .mate y x
  mate_total : ∀ x, ∃! y, edge C .mate x y
  mate_equiv : ∀ x y, edge C .mate x y → edge C .equiv x y

abbrev pairedClass : StructureClass (L := Lang) :=
  fun {_} C => IsPairedEquivalence C

abbrev A : RelStructure Lang (Fin 4) where
  rel
    | .lt, t => (t 0).val < (t 1).val
    | .equiv, t => (t 0).val / 2 = (t 1).val / 2
    | .mate, t => (t 0).val / 2 = (t 1).val / 2 ∧ t 0 ≠ t 1

abbrev B : RelStructure Lang (Fin 6) where
  rel
    | .lt, t => (t 0).val < (t 1).val
    | .equiv, t => ((t 0).val / 2 = 1 ↔ (t 1).val / 2 = 1)
    | .mate, t => (t 0).val / 2 = (t 1).val / 2 ∧ t 0 ≠ t 1

theorem A_mem : pairedClass A := by
  constructor
  · decide
  · decide
  · decide
  · exact ⟨by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

theorem B_mem : pairedClass B := by
  constructor
  · decide
  · decide
  · decide
  · exact ⟨by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

/-- The first two matched pairs form A. -/
def first : Embedding A B where
  toFun x := ⟨x.val, by omega⟩
  injective := by
    intro x y h
    apply Fin.ext
    exact congrArg Fin.val h
  map_rel_iff := by decide

/-- The last two matched pairs form A, in the reversed E-class order. -/
def last : Embedding A B where
  toFun x := ⟨x.val + 2, by omega⟩
  injective := by
    intro x y h
    have hh := congrArg Fin.val h
    apply Fin.ext
    change x.val + 2 = y.val + 2 at hh
    omega
  map_rel_iff := by decide

/-- Finite equivalence relations admit natural-number class labels.
No order or matching hypothesis is needed for this fact. -/
theorem exists_class_labels {V : Type} [Finite V]
    (C : RelStructure Lang V) (hE : Equivalence (edge C .equiv)) :
    ∃ q : V → ℕ, ∀ x y, q x = q y ↔ edge C .equiv x y := by
  classical
  let s : Setoid V := ⟨edge C .equiv, hE⟩
  letI : Fintype (Quotient s) := Fintype.ofFinite (Quotient s)
  let q : V → ℕ := fun x =>
    ((Fintype.equivFin (Quotient s)) (Quotient.mk s x)).val
  refine ⟨q, ?_⟩
  intro x y
  constructor
  · intro h
    apply Quotient.exact
    apply (Fintype.equivFin (Quotient s)).injective
    exact Fin.ext h
  · intro h
    have he : Quotient.mk s x = Quotient.mk s y := Quotient.sound h
    exact congrArg (fun z : Quotient s =>
      ((Fintype.equivFin (Quotient s)) z).val) he

/-- The two displayed A-copies in every B-copy have opposite colours. -/
theorem not_arrow_of_class_labels {V : Type}
    (C : RelStructure Lang V) (q : V → ℕ)
    (hq : ∀ x y, q x = q y ↔ edge C .equiv x y) :
    ¬ StructuralRamsey.Arrow A B C Bool := by
  classical
  let colour : Embedding A C → Bool := fun a => decide (q (a 0) < q (a 2))
  intro hArrow
  obtain ⟨b, hMono⟩ := hArrow colour
  have h04 : q (b 0) = q (b 4) := by
    apply (hq _ _).mpr
    exact (b.map_rel_iff .equiv ![0, 4]).mpr (by decide)
  have h02 : q (b 0) ≠ q (b 2) := by
    intro h
    have he : edge C .equiv (b 0) (b 2) := (hq _ _).mp h
    have hf : B.rel .equiv ![0, 2] :=
      (b.map_rel_iff .equiv ![0, 2]).mp he
    exact (by decide : ¬ B.rel .equiv ![0, 2]) hf
  have hm := hMono first last
  change decide (q (b 0) < q (b 2)) = decide (q (b 2) < q (b 4)) at hm
  rw [← h04] at hm
  by_cases hlt : q (b 0) < q (b 2)
  · have hn : ¬ q (b 2) < q (b 0) := by omega
    simp [hlt, hn] at hm
  · have hgt : q (b 2) < q (b 0) := by omega
    simp [hlt, hgt] at hm

/-- There is no finite Ramsey witness in the paired-equivalence class. -/
theorem no_finite_ramsey_witness {V : Type} [Finite V]
    (C : RelStructure Lang V) (hC : pairedClass C) :
    ¬ StructuralRamsey.Arrow A B C Bool := by
  obtain ⟨q, hq⟩ := exists_class_labels C hC.equiv
  exact not_arrow_of_class_labels C q hq

/-- Total loop-free matching excludes every one-element structure. -/
theorem no_singleton_member {V : Type} [Nonempty V] [Subsingleton V]
    (C : RelStructure Lang V) : ¬ pairedClass C := by
  intro hC
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  obtain ⟨y, hy, _⟩ := hC.mate_total x
  have hxy : y = x := Subsingleton.elim _ _
  subst y
  exact hC.mate_irrefl x hy

/-- The literal 2019 membership antecedent admits only empty C. -/
theorem literal_test_membership_forces_empty
    {V : Type} (C : RelStructure Lang V)
    (rules : ClosureDescription Lang)
    (hAll : ∀ S : Set V,
      IsUIrreducible rules (C.induce S) → pairedClass (C.induce S)) :
    IsEmpty V :=
  isEmpty_of_intrinsic_tests_mem_of_no_singletons C no_singleton_member hAll

/-- For this class the literal local-finiteness CONCLUSION follows
from (4b) alone, for any closure description whatsoever. -/
theorem literal_copywise_completion_is_automatic
    {V W : Type} (C : RelStructure Lang V)
    (D : RelStructure Lang W) [Finite W] (hD : pairedClass D)
    (rules : ClosureDescription Lang)
    (hAll : ∀ S : Set V,
      IsUIrreducible rules (C.induce S) → pairedClass (C.induce S)) :
    HasCopywiseCompletion pairedClass D C :=
  copywiseCompletion_of_intrinsic_tests_mem_of_no_singletons
    D hD C no_singleton_member hAll

end StructuralRamsey.RelStructure.PairedEquivalenceObstruction

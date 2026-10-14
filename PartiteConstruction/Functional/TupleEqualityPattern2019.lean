import PartiteConstruction.Functional.PartialDomainEncoding

/-!
# Exact equality patterns of finite function-input tuples (2019 encoding)

The 2019 closure-description translation of a partial function cannot
assume that its input coordinates are distinct. An arbitrary tuple
x : Fin a -> V factors as a surjective equality-pattern map
r : Fin a -> Fin m followed by an injective enumeration of the
DISTINCT original input vertices.

We deliberately do not identify the root carrier Fin m with the
possibly longer original argument tuple Fin a.  The root of a closure
rule must use the m distinct vertices; r records repetitions.

The following proof constructs this data on the exact input vertices
with no closure hull and no assumption that a>0. The empty-input case
has m=0 and will be handled by the separate nullary-root reduction,
since the 2019 closure-description rules require positive root size.
-/

namespace StructuralRamsey.Structure

universe v
variable {V : Type v}

/-- Every finite input tuple factors through the set of its distinct
values. The first map records ALL coordinate repetitions and is
surjective; the second is an injective enumeration of precisely
those vertices. -/
theorem exists_tuple_equality_pattern
    {a : ℕ} [Finite V] (x : Fin a → V) :
    ∃ (m : ℕ) (r : Fin a → Fin m) (e : Fin m → V),
      Function.Surjective r ∧ Function.Injective e ∧
      (∀ i : Fin a, x i = e (r i)) := by
  classical
  let S : Set V := Set.range x
  letI : Fintype S := Fintype.ofFinite S
  let equiv : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let m : ℕ := Fintype.card S
  let r : Fin a → Fin m := fun i => equiv ⟨x i, ⟨i, rfl⟩⟩
  let e : Fin m → V := fun j => (equiv.symm j).1
  refine ⟨m, r, e, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := (equiv.symm j).2
    refine ⟨i, ?_⟩
    change equiv ⟨x i, ⟨i, rfl⟩⟩ = j
    have heq : (⟨x i, ⟨i, rfl⟩⟩ : S) = equiv.symm j :=
      Subtype.ext hi
    rw [heq]
    exact equiv.apply_symm_apply j
  · intro i j hij
    have h : equiv.symm i = equiv.symm j := Subtype.ext hij
    exact equiv.symm.injective h
  · intro i
    change x i = (equiv.symm (equiv ⟨x i, ⟨i, rfl⟩⟩)).1
    rw [equiv.symm_apply_apply]


/-- The factorization records EXACTLY the equality pattern:
two original argument positions agree iff their root labels agree.
This is the form used to index distinct closure symbols for
non-injective partial-function inputs. -/
theorem exists_tuple_equality_pattern_exact
    {a : ℕ} [Finite V] (x : Fin a → V) :
    ∃ (m : ℕ) (r : Fin a → Fin m) (e : Fin m → V),
      Function.Surjective r ∧ Function.Injective e ∧
      (∀ i : Fin a, x i = e (r i)) ∧
      (∀ i j : Fin a, x i = x j ↔ r i = r j) := by
  obtain ⟨m, r, e, hSurj, hInj, hFact⟩ :=
    exists_tuple_equality_pattern x
  refine ⟨m, r, e, hSurj, hInj, hFact, ?_⟩
  intro i j
  constructor
  · intro h
    apply hInj
    calc
      e (r i) = x i := (hFact i).symm
      _ = x j := h
      _ = e (r j) := hFact j
  · intro h
    calc
      x i = e (r i) := hFact i
      _ = e (r j) := congrArg e h
      _ = x j := (hFact j).symm

end StructuralRamsey.Structure

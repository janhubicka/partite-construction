import PartiteConstruction.Ramsey.ClosureUIrreducibleMissingRoot

/-! # The missing-output obstruction for intrinsic U-irreducibility

Definition 2.15 (2019) defines U-irreducibility by excluding free
amalgam decompositions into two proper *intrinsically U-closed* sides.
On an arbitrary weak induced test, this is a strictly stronger
indecomposability condition than the relative-U-substructure variant.

A test that contains an embedded closure root but omits every closure
tuple over that root is intrinsically U-irreducible; this remains
true regardless of any additional vertices in the test.

The exact weak test below is NOT replaced by a generated closure hull.
Together with finite-cardinality bounds, this gives a useful obstruction
to an unqualified assertion that all intrinsic U-irreducible weak tests
embed in one fixed finite B.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {V W : Type v}

/-- An induced weak test that contains an embedded prescribed root but
omits every closure tuple extending that root is intrinsically
U-irreducible, irrespective of the other tested vertices. -/
theorem IsUIrreducible.of_missing_tuple_in_weak_test
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root A)
    (S : Set V)
    (hRoot : ∀ k : Fin rule.rootSize, e k ∈ S)
    (hMissing :
      ∀ t : Fin (L.arity rule.symbol) → V,
        A.rel rule.symbol t →
        (∀ k : Fin rule.rootSize,
          t (k.castLE rule.rootLE) = e k) →
        ∃ j : Fin (L.arity rule.symbol), t j ∉ S) :
    IsUIrreducible rules (A.induce S) := by
  let eS : Embedding rule.root (A.induce S) := {
    toFun := fun k => ⟨e k, hRoot k⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change A.rel R (e ∘ x) ↔ rule.root.rel R x
      exact e.map_rel_iff R x
  }
  have hNoTuple :
      ¬ ∃ t : Fin (L.arity rule.symbol) → S,
          (A.induce S).rel rule.symbol t ∧
          ∀ k : Fin rule.rootSize,
            t (k.castLE rule.rootLE) = eS k := by
    rintro ⟨t, ht, hte⟩
    have htA : A.rel rule.symbol (Subtype.val ∘ t) := ht
    have htRoot : ∀ k : Fin rule.rootSize,
        (Subtype.val ∘ t) (k.castLE rule.rootLE) = e k := by
      intro k
      exact congrArg Subtype.val (hte k)
    obtain ⟨j, hj⟩ := hMissing (Subtype.val ∘ t) htA htRoot
    exact hj (t j).2
  intro H E F Root Left Right sL sR iL iR hLeft hRight hFree
  exact (IsUIrreducible.of_missing_closureTuple
    rule hrule eS hNoTuple) hLeft hRight hFree

/-- Intrinsic U-irreducible induced tests of A all embed into B.
This is the literal 'every U-irreducible substructure is a
substructure of B' property, without adding a U-closedness condition
on the tested source. -/
def AllIntrinsicUIrreducibleTestsEmbed
    (rules : ClosureDescription L)
    (A : RelStructure L V) (B : RelStructure L W) : Prop :=
  ∀ S : Set V,
    IsUIrreducible rules (A.induce S) →
      Nonempty (Embedding (A.induce S) B)

/-- Any missing-closure-root test larger than B refutes the literal
intrinsic-U-irreducible coverage property. This is a conditional
obstruction and does not itself construct a forbidden Ramsey witness. -/
theorem not_allIntrinsicUIrreducibleTestsEmbed_of_large_missing_test
    [Fintype W]
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root A)
    (S : Set V) [Fintype S]
    (hRoot : ∀ k : Fin rule.rootSize, e k ∈ S)
    (hMissing :
      ∀ t : Fin (L.arity rule.symbol) → V,
        A.rel rule.symbol t →
        (∀ k : Fin rule.rootSize,
          t (k.castLE rule.rootLE) = e k) →
        ∃ j : Fin (L.arity rule.symbol), t j ∉ S)
    (hLarge : Fintype.card W < Fintype.card S) :
    ¬ AllIntrinsicUIrreducibleTestsEmbed rules A B := by
  intro hCover
  have hIrred : IsUIrreducible rules (A.induce S) :=
    IsUIrreducible.of_missing_tuple_in_weak_test
      rule hrule e S hRoot hMissing
  obtain ⟨j⟩ := hCover S hIrred
  have hBound : Fintype.card S ≤ Fintype.card W :=
    Fintype.card_le_of_injective j j.injective
  exact (Nat.not_le_of_gt hLarge) hBound

end StructuralRamsey.RelStructure

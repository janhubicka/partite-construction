import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-! # U-semi-closed relational structures (2019, Definition 2.24)

The closure rule need not be total on every embedded root during the
partite construction. Its partial closure relation must nevertheless
remain single-valued on each root and never contain a tuple whose
designated root fails to embed.

This is the original *relational* U-semi-closedness of Hubička--Nešetřil
(2019), not the later total-set-valued-function semantics.

Every induced structure on an arbitrary vertex set of a U-closed
structure is U-semi-closed. This induction is **vertex-exact**: the
tested set is neither functionally closed nor replaced by its closure
hull, and its cardinality is unchanged.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {V : Type v}

/-- A closure relation is partial and functional above valid embedded
root tuples, and is nowhere defined above invalid root tuples.

The uniqueness clause compares *entire* closure tuples, with no
assumption that the output positions are outside the root. -/
def ClosureRule.IsSemiClosed
    (rule : ClosureRule L) (A : RelStructure L V) : Prop :=
  (∀ t : Fin (L.arity rule.symbol) → V,
      A.rel rule.symbol t → rule.RootMatches A t) ∧
  (∀ t₁ t₂ : Fin (L.arity rule.symbol) → V,
      A.rel rule.symbol t₁ →
      A.rel rule.symbol t₂ →
      (∀ i : Fin rule.rootSize,
         t₁ (i.castLE rule.rootLE) =
         t₂ (i.castLE rule.rootLE)) →
      t₁ = t₂)

/-- The U-semi-closed property is imposed independently at every
closure rule, allowing any number of rules per relation symbol. -/
def IsUSemiClosed
    (rules : ClosureDescription L)
    (A : RelStructure L V) : Prop :=
  ∀ rule : ClosureRule L, rule ∈ rules → rule.IsSemiClosed A

/-- Full closedness implies the corresponding partial uniqueness and
root-validity statements; no finiteness is assumed. -/
theorem ClosureRule.IsClosed.isSemiClosed
    {rule : ClosureRule L} {A : RelStructure L V}
    (h : rule.IsClosed A) :
    rule.IsSemiClosed A := by
  refine ⟨h.1, ?_⟩
  intro t₁ t₂ ht₁ ht₂ hroot
  obtain ⟨e, he⟩ := h.1 t₁ ht₁
  obtain ⟨t, ht, hunique⟩ := h.2 e
  have hEq₁ : t₁ = t :=
    hunique t₁ ⟨ht₁, he⟩
  have hEq₂ : t₂ = t :=
    hunique t₂ ⟨ht₂, fun i =>
      (hroot i).symm.trans (he i)⟩
  exact hEq₁.trans hEq₂.symm

/-- Semiclosedness is hereditary under arbitrary **weak vertex
induction**: no root/output closure hull is taken. -/
theorem ClosureRule.IsSemiClosed.induce
    {rule : ClosureRule L} {A : RelStructure L V}
    (h : rule.IsSemiClosed A)
    (S : Set V) :
    rule.IsSemiClosed (A.induce S) := by
  constructor
  · intro t ht
    have htA : A.rel rule.symbol (Subtype.val ∘ t) := ht
    obtain ⟨e, he⟩ := h.1 (Subtype.val ∘ t) htA
    have heS : ∀ i : Fin rule.rootSize, e i ∈ S := by
      intro i
      rw [← he i]
      exact (t (i.castLE rule.rootLE)).2
    let eS : Embedding rule.root (A.induce S) := {
      toFun := fun i => ⟨e i, heS i⟩
      injective := by
        intro x y hxy
        apply e.injective
        exact congrArg Subtype.val hxy
      map_rel_iff := by
        intro R x
        change A.rel R (e ∘ x) ↔ rule.root.rel R x
        exact e.map_rel_iff R x
    }
    refine ⟨eS, ?_⟩
    intro i
    apply Subtype.ext
    exact he i
  · intro t₁ t₂ ht₁ ht₂ hroot
    have htA₁ : A.rel rule.symbol (Subtype.val ∘ t₁) := ht₁
    have htA₂ : A.rel rule.symbol (Subtype.val ∘ t₂) := ht₂
    have hRootA :
        ∀ i : Fin rule.rootSize,
          (Subtype.val ∘ t₁) (i.castLE rule.rootLE) =
          (Subtype.val ∘ t₂) (i.castLE rule.rootLE) := by
      intro i
      exact congrArg Subtype.val (hroot i)
    have heq : (Subtype.val ∘ t₁) = (Subtype.val ∘ t₂) :=
      h.2 _ _ htA₁ htA₂ hRootA
    funext j
    apply Subtype.ext
    exact congrFun heq j

/-- Partial uniqueness plus existence of a closure tuple above
each embedded root is exactly full U-closedness for one rule. -/
theorem ClosureRule.IsSemiClosed.isClosed_of_exists
    {rule : ClosureRule L} {A : RelStructure L V}
    (h : rule.IsSemiClosed A)
    (hExists : ∀ e : Embedding rule.root A,
       ∃ t : Fin (L.arity rule.symbol) → V,
         A.rel rule.symbol t ∧
         ∀ i : Fin rule.rootSize,
           t (i.castLE rule.rootLE) = e i) :
    rule.IsClosed A := by
  refine ⟨h.1, ?_⟩
  intro e
  obtain ⟨t, ht⟩ := hExists e
  refine ⟨t, ht, ?_⟩
  intro z hz
  apply h.2 z t hz.1 ht.1
  intro i
  exact (hz.2 i).trans (ht.2 i).symm

/-- A U-closed structure is U-semi-closed. -/
theorem IsUClosed.isUSemiClosed
    {rules : ClosureDescription L} {A : RelStructure L V}
    (h : IsUClosed rules A) :
    IsUSemiClosed rules A := by
  intro rule hrule
  exact (h rule hrule).isSemiClosed

/-- All arbitrary induced weak vertex tests of a U-semi-closed
structure remain U-semi-closed; this is the direct hereditary
property needed during the Picture step. -/
theorem IsUSemiClosed.induce
    {rules : ClosureDescription L} {A : RelStructure L V}
    (h : IsUSemiClosed rules A) (S : Set V) :
    IsUSemiClosed rules (A.induce S) := by
  intro rule hrule
  exact (h rule hrule).induce S

/-- In particular, *every* induced vertex set in a U-closed
structure is U-semi-closed. The input set is used exactly as given. -/
theorem IsUClosed.induce_isUSemiClosed
    {rules : ClosureDescription L} {A : RelStructure L V}
    (h : IsUClosed rules A) (S : Set V) :
    IsUSemiClosed rules (A.induce S) :=
  h.isUSemiClosed.induce S

/-- Reconstruct U-closedness from the U-semi-closed invariant and
the remaining *totality over embedded roots* condition. -/
theorem IsUSemiClosed.isUClosed_of_exists
    {rules : ClosureDescription L} {A : RelStructure L V}
    (h : IsUSemiClosed rules A)
    (hExists : ∀ (rule : ClosureRule L), rule ∈ rules →
      ∀ e : Embedding rule.root A,
        ∃ t : Fin (L.arity rule.symbol) → V,
          A.rel rule.symbol t ∧
          ∀ i : Fin rule.rootSize,
            t (i.castLE rule.rootLE) = e i) :
    IsUClosed rules A := by
  intro rule hrule
  exact (h rule hrule).isClosed_of_exists (hExists rule hrule)

end StructuralRamsey.RelStructure

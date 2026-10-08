import PartiteConstruction.Relational.Homomorphism

/-! # General closure descriptions of All those Ramsey classes

The 2019 Hubička--Nešetřil closure description is relational:
a closure rule associates a relation symbol R^U to a finite
**irreducible root structure** R of positive vertex size. A tuple
in the relation has the vertices of its root as an initial segment.

A U-closed structure has exactly one closure tuple over each embedded
root and no closure tuple whose root fails to embed. This file records
the genuine relational rule interface, rather than replacing it
by functions whose roots are necessarily input tuples or using the
total-fibre homomorphism convention of the later survey.

A U-substructure is *not* defined by taking a generated closure:
it is the induced structure on the EXACT given vertex set S, with the
condition that every closure tuple whose root lies in S also lies in
S. This makes the size of a weak test the cardinality of S.

The first goal is the substructure/closedness equivalence of
All those Ramsey classes, Lemma 2.23(1), not the full
multiamalgamation theorem.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- One relational closure rule. The initial `rootSize` coordinates
of a closure-relation tuple form a copy of `root`.
The positive root size matches the convention of the 2019 paper. -/
structure ClosureRule (L : RelLanguage.{u}) where
  symbol : L.Symbol
  rootSize : ℕ
  rootPositive : 0 < rootSize
  rootLE : rootSize ≤ L.arity symbol
  root : RelStructure L (Fin rootSize)
  rootIrreducible : root.Irreducible

/-- A relational closure description, allowing several rules. -/
abbrev ClosureDescription (L : RelLanguage.{u}) :=
  Set (ClosureRule L)

/-- A closure tuple has its first coordinates equal to the image of
an honest induced embedding of its prescribed root. -/
def ClosureRule.RootMatches
    (rule : ClosureRule L)
    (A : RelStructure L V)
    (t : Fin (L.arity rule.symbol) → V) : Prop :=
  ∃ e : Embedding rule.root A,
    ∀ i : Fin rule.rootSize, t (i.castLE rule.rootLE) = e i

/-- The closure relation of a rule is exactly one tuple over each
copy of its prescribed root and never appears over a non-root tuple.
This is the relational formulation of the 2019 U-closed condition. -/
def ClosureRule.IsClosed
    (rule : ClosureRule L)
    (A : RelStructure L V) : Prop :=
  (∀ t, A.rel rule.symbol t → rule.RootMatches A t) ∧
  (∀ e : Embedding rule.root A,
    ∃! t : Fin (L.arity rule.symbol) → V,
      A.rel rule.symbol t ∧
      ∀ i : Fin rule.rootSize,
        t (i.castLE rule.rootLE) = e i)

/-- A finite or infinite structure is U-closed when it satisfies each
closure rule. No finiteness hypothesis is needed for this definition. -/
def IsUClosed
    (rules : ClosureDescription L) (A : RelStructure L V) : Prop :=
  ∀ rule : ClosureRule L, rule ∈ rules → rule.IsClosed A

/-- The vertex-exact notion of a U-substructure: a closure-relation
tuple cannot leave S if all of its designated root vertices are in S.
In particular S is NOT enlarged to its generated closure. -/
def IsUSubstructure
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) : Prop :=
  ∀ (rule : ClosureRule L), rule ∈ rules →
    ∀ (t : Fin (L.arity rule.symbol) → V),
      A.rel rule.symbol t →
      (∀ i : Fin rule.rootSize,
        t (i.castLE rule.rootLE) ∈ S) →
      ∀ j : Fin (L.arity rule.symbol), t j ∈ S

/-- An induced U-substructure of a U-closed structure is itself
U-closed. This is the first implication of Lemma 2.23(1). -/
theorem IsUClosed.induce_of_USubstructure
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hA : IsUClosed rules A)
    (S : Set V) (hS : IsUSubstructure rules A S) :
    IsUClosed rules (A.induce S) := by
  intro rule hrule
  constructor
  · intro t hTuple
    have hTupleA : A.rel rule.symbol (Subtype.val ∘ t) := hTuple
    obtain ⟨e,he⟩ := (hA rule hrule).1
      (Subtype.val ∘ t) hTupleA
    let eS : Embedding rule.root (A.induce S) := {
      toFun := fun i => ⟨e i, by
        rw [← he i]
        exact (t (i.castLE rule.rootLE)).2⟩
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
  · intro eS
    let eA : Embedding rule.root A :=
      (inclusion A S).comp eS
    obtain ⟨t,ht,hUnique⟩ := (hA rule hrule).2 eA
    have hRootS : ∀ i : Fin rule.rootSize,
        t (i.castLE rule.rootLE) ∈ S := by
      intro i
      rw [ht.2 i]
      exact (eS i).2
    have hAllS : ∀ j : Fin (L.arity rule.symbol),
        t j ∈ S := hS rule hrule t ht.1 hRootS
    let tS : Fin (L.arity rule.symbol) → S :=
      fun j => ⟨t j,hAllS j⟩
    refine ⟨tS, ⟨?_, ?_⟩, ?_⟩
    · change A.rel rule.symbol (Subtype.val ∘ tS)
      have heq : Subtype.val ∘ tS = t := rfl
      rw [heq]
      exact ht.1
    · intro i
      apply Subtype.ext
      exact ht.2 i
    · intro z hz
      have hzA : A.rel rule.symbol
          (Subtype.val ∘ z) := hz.1
      have hzRootA : ∀ i : Fin rule.rootSize,
          (Subtype.val ∘ z) (i.castLE rule.rootLE) = eA i := by
        intro i
        exact congrArg Subtype.val (hz.2 i)
      have hzEq : (Subtype.val ∘ z) = t :=
        hUnique _ ⟨hzA,hzRootA⟩
      funext i
      apply Subtype.ext
      exact congrFun hzEq i

/-- Conversely, if both the ambient structure and its induced
substructure are U-closed, S is a U-substructure of A. This is
the reverse implication of Lemma 2.23(1). -/
theorem IsUClosed.USubstructure_of_induce
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hA : IsUClosed rules A)
    (S : Set V)
    (hInd : IsUClosed rules (A.induce S)) :
    IsUSubstructure rules A S := by
  intro rule hrule t ht hRootS j
  obtain ⟨e,he⟩ := (hA rule hrule).1 t ht
  have heS : ∀ i : Fin rule.rootSize, e i ∈ S := by
    intro i
    rw [← he i]
    exact hRootS i
  let eS : Embedding rule.root (A.induce S) := {
    toFun := fun i => ⟨e i,heS i⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change A.rel R (e ∘ x) ↔ rule.root.rel R x
      exact e.map_rel_iff R x
  }
  obtain ⟨z,hz,_⟩ := (hInd rule hrule).2 eS
  have hza : A.rel rule.symbol (Subtype.val ∘ z) := hz.1
  have hzRootA : ∀ i : Fin rule.rootSize,
      (Subtype.val ∘ z) (i.castLE rule.rootLE) = e i := by
    intro i
    exact congrArg Subtype.val (hz.2 i)
  obtain ⟨q,hq,hUnique⟩ := (hA rule hrule).2 e
  have htq : t = q := hUnique t ⟨ht,he⟩
  have hzq : (Subtype.val ∘ z) = q :=
    hUnique (Subtype.val ∘ z) ⟨hza,hzRootA⟩
  have htEq : t = Subtype.val ∘ z := htq.trans hzq.symm
  rw [htEq]
  exact (z j).2

/-- All those Ramsey classes, Lemma 2.23(1): inside a U-closed
structure, a vertex-exact induced substructure is U-closed if and
only if it is a U-substructure of its ambient structure. -/
theorem IsUClosed.induce_iff_USubstructure
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hA : IsUClosed rules A)
    (S : Set V) :
    IsUClosed rules (A.induce S) ↔
      IsUSubstructure rules A S := by
  constructor
  · exact hA.USubstructure_of_induce S
  · exact hA.induce_of_USubstructure S

end StructuralRamsey.RelStructure

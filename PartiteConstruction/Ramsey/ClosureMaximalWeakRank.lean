import PartiteConstruction.Ramsey.ClosureWeakHullUSize
import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Exact weak tests of maximum U-size are closure-independent

The proposed alternative to the flawed higher-rank increment is to
work with exact WEAK tests of bounded VERTEX cardinality, matching the
repaired local-finiteness hypothesis. The decisive elementary fact is
that a finite weak source whose intrinsic U-size equals its number
of vertices cannot contain any nontrivial closure dependency.

If a tuple has all its root vertices in S but an output x outside S,
the remaining vertices generate x, hence generate the entire weak
source; this would contradict maximal generating rank.

Thus EVERY exact vertex subset is relatively U-closed. On a closed
irreducible test embedded in such a source, this implies that
U-irreducibility is ordinary Gaifman irreducibility. Consequently an
ORDINARY homomorphism-embedding out of a maximal-rank weak source
already protects all CLOSED U-irreducible tests.

These lemmas are not themselves the full weak-size Picture increment:
that still requires the true free-cut separation and all
small-side completions in the actual multi-line attachment.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W X : Type v}

/-- If U-size is the full vertex cardinality, EVERY subset of the
weak source is a relative U-substructure. Source closedness is NOT
assumed. A violation would exhibit a redundant vertex that can be
deleted from a generating set. -/
theorem all_subsets_relative_of_USize_eq_card
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hMax : USize rules A = Fintype.card V) :
    ∀ S : Set V, IsUSubstructure rules A S := by
  classical
  intro S rule hrule t ht hRoot j
  by_contra hOut
  let y : V := t j
  let G : Finset V := Finset.univ.erase y
  have hRootG (i : Fin rule.rootSize) : t (i.castLE rule.rootLE) ∈
      (↑G : Set V) := by
    apply Finset.mem_erase.mpr
    constructor
    · intro hEq
      apply hOut
      have hMem : y ∈ S := hEq ▸ hRoot i
      exact hMem
    · exact Finset.mem_univ _
  have hGen : IsUGenerating rules A (↑G : Set V) := by
    change UClosureHull rules A (↑G : Set V) = Set.univ
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxy : x = y
    · subst x
      have hCl := UClosureHull_isUSubstructure rules A (↑G : Set V)
      change t j ∈ UClosureHull rules A (↑G : Set V)
      exact hCl rule hrule t ht
        (fun i => subset_UClosureHull rules A (↑G : Set V)
          (hRootG i)) j
    · exact subset_UClosureHull rules A (↑G : Set V)
        (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ _⟩)
  have hBound : USize rules A ≤ G.card :=
    USize_le_of_generating rules A G hGen
  have hErase : G.card < Fintype.card V := by
    have hy : y ∈ (Finset.univ : Finset V) := Finset.mem_univ y
    have heq := Finset.card_erase_of_mem hy
    have hpos : 0 < (Finset.univ : Finset V).card :=
      Finset.card_pos.mpr ⟨y, hy⟩
    have hcard : (Finset.univ : Finset V).card = Fintype.card V :=
      Finset.card_univ
    dsimp [G]
    omega
  omega

/-- On a U-closed source with EVERY subset relatively closed,
intrinsic U-irreducibility collapses to ordinary irreducibility.
The reverse implication (ordinary implies U-irreducible) is always
true; here we establish the converse for closure-independent
structures. -/
theorem IsUIrreducible.irreducible_of_all_subsets_relative
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hClosed : IsUClosed rules A)
    (hIrred : IsUIrreducible rules A)
    (hAll : ∀ S : Set V, IsUSubstructure rules A S) :
    A.Irreducible := by
  intro x y hxy
  by_contra hNo
  let S : Set V := {z | z ≠ x}
  let T : Set V := {z | z ≠ y}
  have hCover : ∀ z : V, z ∈ S ∨ z ∈ T := by
    intro z
    by_cases hzx : z = x
    · right
      change z ≠ y
      exact hzx ▸ hxy
    · exact Or.inl hzx
  have hTuples : ∀ R (z : Fin (L.arity R) → V), A.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T) := by
    intro R z hz
    by_cases hAllS : ∀ k, z k ≠ x
    · exact Or.inl hAllS
    · right
      push_neg at hAllS
      obtain ⟨i, hzi⟩ := hAllS
      intro k
      change z k ≠ y
      by_contra hzk
      have hzy : z k = y := not_ne_iff.mp hzk
      exact hNo ⟨R, z, i, k, hz, hzi, hzy⟩
  rcases hIrred.closed_cover hClosed S T
    (hAll S) (hAll T) hCover hTuples with hS | hT
  · exact (hS x) rfl
  · exact (hT y) rfl

/-- An embedded CLOSED U-irreducible test of a maximum-rank WEAK
structure is in fact ordinarily irreducible, even though the whole
source need not be U-closed. The exact test carrier is preserved. -/
theorem closed_test_irreducible_of_max_USize
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hMax : USize rules A = Fintype.card V)
    (Test : RelStructure L X)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : Embedding Test A) :
    Test.Irreducible := by
  have hAllA := all_subsets_relative_of_USize_eq_card rules A hMax
  have hAllTest : ∀ S : Set X, IsUSubstructure rules Test S := by
    intro S rule hrule t ht hRoot j
    have hRel : A.rel rule.symbol (e ∘ t) :=
      (e.map_rel_iff rule.symbol t).mpr ht
    have hRangeRoot : ∀ i : Fin rule.rootSize,
        (e ∘ t) (i.castLE rule.rootLE) ∈ e '' S := by
      intro i
      exact ⟨t (i.castLE rule.rootLE), hRoot i, rfl⟩
    obtain ⟨x, hx, heq⟩ :=
      hAllA (e '' S) rule hrule (e ∘ t) hRel hRangeRoot j
    have htEq : t j = x := (e.injective heq).symm
    exact htEq ▸ hx
  exact hIrred.irreducible_of_all_subsets_relative hClosed hAllTest

/-- In the full-rank weak branch an ORDINARY relational
homomorphism-embedding is already a working CLOSED-test
U-homomorphism-embedding. This is exactly what lets an ordinary
partite projection suffice for this branch in a potential
weak-vertex-cardinality induction. -/
theorem IsHomomorphismEmbedding.toClosedMap_of_max_USize
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W}
    [Fintype V]
    (hf : A.IsHomomorphismEmbedding B f)
    (hMax : USize rules A = Fintype.card V) :
    IsClosedUHomomorphismEmbedding rules A B f := by
  constructor
  · exact hf.1
  · intro X Test hClosed hIrred e
    have hOrd := closed_test_irreducible_of_max_USize
      rules A hMax Test hClosed hIrred e
    exact hf.after_irreducible_embedding hOrd e

end StructuralRamsey.RelStructure

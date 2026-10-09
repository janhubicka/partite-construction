import PartiteConstruction.Ramsey.ClosureWeakTestIntrinsicObstruction

/-! # A non-vacuity obstruction in the literal 2019 local-finiteness axiom

Published Definition 2.17(4b) quantifies over *every* U-irreducible
substructure, including nonclosed induced weak tests (Definition 2.15).
If an ambient U-closed structure contains a genuine closure output
outside its prescribed root, removing that output gives a nonclosed
U-irreducible induced test.

Consequently the literal (4b) membership premise cannot hold for such
an ambient C when every member of K is U-closed. This is a GENERIC
obstruction, not a concrete counterexample to the whole Theorem 2.18:
the local-finiteness axiom is an implication and can be vacuous on C
with such closure tuples.

No source set is enlarged, and the original published predicates are
used unchanged. The uniqueness part of U-closedness is indispensable.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Removing a genuine closure output produces a vertex-exact induced
substructure which is both intrinsically U-irreducible and nonclosed. -/
theorem IsUClosed.exists_nonclosed_Uirreducible_test
    {rules : ClosureDescription L} {C : RelStructure L V}
    (hC : IsUClosed rules C)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root C)
    (t : Fin (L.arity rule.symbol) → V)
    (ht : C.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize, t (k.castLE rule.rootLE) = e k)
    (j : Fin (L.arity rule.symbol))
    (hGenuine : ∀ k : Fin rule.rootSize, t j ≠ e k) :
    ∃ S : Set V,
      IsUIrreducible rules (C.induce S) ∧
      ¬ IsUClosed rules (C.induce S) := by
  let S : Set V := {x | x ≠ t j}
  have hRoot (k : Fin rule.rootSize) : e k ∈ S :=
    (hGenuine k).symm
  obtain ⟨u, hu, hUnique⟩ := (hC rule hrule).2 e
  have htu : t = u := hUnique t ht
  have hMissing :
      ∀ s : Fin (L.arity rule.symbol) → V,
        C.rel rule.symbol s →
        (∀ k : Fin rule.rootSize,
          s (k.castLE rule.rootLE) = e k) →
        ∃ l : Fin (L.arity rule.symbol), s l ∉ S := by
    intro s hs hsRoot
    have hsu : s = u := hUnique s ⟨hs, hsRoot⟩
    have hst : s = t := hsu.trans htu.symm
    refine ⟨j, ?_⟩
    intro hne
    exact hne (congrFun hst j)
  have hIrred : IsUIrreducible rules (C.induce S) :=
    IsUIrreducible.of_missing_tuple_in_weak_test
      rule hrule e S hRoot hMissing
  refine ⟨S, hIrred, ?_⟩
  intro hClosed
  have hSClosed : IsUSubstructure rules C S :=
    hC.USubstructure_of_induce S hClosed
  have hRootTuple : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) ∈ S := by
    intro k
    rw [ht.2 k]
    exact hRoot k
  have hj : t j ∈ S :=
    hSClosed rule hrule t ht.1 hRootTuple j
  exact hj rfl

/-- The literal "all U-irreducible induced tests lie in K" condition
fails in the presence of any genuine closure output, because K only
contains intrinsically U-closed structures. This is directly the
logical obstruction to using Definition 2.17(4b) as printed. -/
theorem not_all_intrinsic_Uirred_tests_in_closed_class
    {rules : ClosureDescription L} {C : RelStructure L V}
    {K : StructureClass.{u,v} (L := L)}
    (hKClosed : ∀ {W : Type v} (D : RelStructure L W),
      K D → IsUClosed rules D)
    (hC : IsUClosed rules C)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root C)
    (t : Fin (L.arity rule.symbol) → V)
    (ht : C.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize, t (k.castLE rule.rootLE) = e k)
    (j : Fin (L.arity rule.symbol))
    (hGenuine : ∀ k : Fin rule.rootSize, t j ≠ e k) :
    ¬ (∀ S : Set V, IsUIrreducible rules (C.induce S) →
          K (C.induce S)) := by
  intro hAll
  obtain ⟨S, hIrred, hNonclosed⟩ :=
    hC.exists_nonclosed_Uirreducible_test rule hrule e t ht j hGenuine
  exact hNonclosed (hKClosed (C.induce S) (hAll S hIrred))

end StructuralRamsey.RelStructure

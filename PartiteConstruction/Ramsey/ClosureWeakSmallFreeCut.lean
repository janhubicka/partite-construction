import PartiteConstruction.Ramsey.ClosureWeakRankDichotomy
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Relational.FreeAmalgamationClass

/-!
# Exact weak tests reduce to a small proper free cut

This combines the two checked positive facts from the repaired
multiamalgamation proof:

(1) Given the rank-j completion invariant for closed substructures
    of a U-closed picture C, every exact weak test on <=j+1
    vertices is either already completable, or has exactly
    j+1 vertices and maximal intrinsic U-size.
    (ClosureWeakRankDichotomy, merged PR #212.)

(2) Every ordinary irreducible exact weak test in C has a corrected
    K-completion from coverage of closed U-irreducible tests by
    one original ordinary irreducible Base∈K.
    (ClosureWeakIrreducibleCoverage, merged PR #215.)

It follows that any *remaining* noncompletable exact weak test
F has maximal U-size and is ORDINARY REDUCIBLE. Such an F has
an actual proper free amalgam decomposition into two induced
proper sides. Both side ranges are relatively U-closed in F,
because F has maximal rank, and both sides have at most j
vertices by the proper embedding cardinality inequality.

This is the exact geometric input needed for a weak-cardinality
completion induction. IT DOES NOT say that the common induced
root lies in K or is intrinsically U-closed. The existing strong
K-amalgamation and generated-K-boundary lemmas can glue the
side completions only after a compatible *closed K-boundary*
has been supplied. That boundary is still a genuine missing
Hales--Jewett-history obligation.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W : Type v}

/-- With the usual previous closed-rank-j completion and original
B-copy coverage invariants, an exact weak test on at most j+1
vertices is EITHER already K-completable, OR has a genuine proper
free decomposition with relatively U-closed proper side ranges
of at most j vertices.

The conclusion contains NO assumption that the separator/root of
this decomposition is closed or belongs to K. This restriction is
essential, rather than a gap concealed behind 'free amalgam'. -/
theorem weak_test_complete_or_small_relative_free_cut
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    [Finite V] [Finite W]
    (C : RelStructure L V) (Base : RelStructure L W)
    (hC : IsUClosed rules C)
    (hBaseK : K Base) (hBaseIrred : Base.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test Base))
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ j →
      HasClosedUKCompletion K rules (C.induce T))
    (S : Finset V) (hCard : S.card ≤ j + 1) :
    HasClosedUKCompletion K rules (C.induce (↑S : Set V)) ∨
      ∃ d : ProperFreeDecomposition (C.induce (↑S : Set V)),
        IsUSubstructure rules (C.induce (↑S : Set V))
          (Set.range d.leftIn) ∧
        IsUSubstructure rules (C.induce (↑S : Set V))
          (Set.range d.rightIn) ∧
        Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j := by
  classical
  rcases weak_test_complete_or_maximal_independent
      C hC j hRank S hCard with
      hDone | ⟨hFull, hMax, hEvery⟩
  · exact Or.inl hDone
  by_cases hIrred : (C.induce (↑S : Set V)).Irreducible
  · exact Or.inl
      (weak_irreducible_completion_of_closed_coverage
        hC hBaseK hBaseIrred hCover
        (↑S : Set V) hIrred)
  · right
    obtain ⟨d⟩ :=
      properFreeDecomposition_of_not_irreducible hIrred
    letI : Finite d.Left :=
      Finite.of_injective d.leftIn d.leftIn.injective
    letI : Finite d.Right :=
      Finite.of_injective d.rightIn d.rightIn.injective
    letI : Fintype d.Left := Fintype.ofFinite d.Left
    letI : Fintype d.Right := Fintype.ofFinite d.Right
    have hLeftCard :
        Fintype.card d.Left < Fintype.card (↑S : Set V) :=
      Fintype.card_lt_of_injective_not_surjective
        d.leftIn d.leftIn.injective d.leftProper
    have hRightCard :
        Fintype.card d.Right < Fintype.card (↑S : Set V) :=
      Fintype.card_lt_of_injective_not_surjective
        d.rightIn d.rightIn.injective d.rightProper
    have hCardS : Fintype.card (↑S : Set V) = S.card := by simp
    have hSmallL : Nat.card d.Left ≤ j := by
      rw [Nat.card_eq_fintype_card]
      omega
    have hSmallR : Nat.card d.Right ≤ j := by
      rw [Nat.card_eq_fintype_card]
      omega
    exact ⟨d, hEvery (Set.range d.leftIn),
      hEvery (Set.range d.rightIn), hSmallL, hSmallR⟩

end StructuralRamsey.RelStructure

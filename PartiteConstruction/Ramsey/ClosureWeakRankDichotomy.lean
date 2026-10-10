import PartiteConstruction.Ramsey.ClosureMaximalWeakRank
import PartiteConstruction.Ramsey.ClosureWeakHullUSize
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# Exact weak-test dichotomy at a finite completion rank cutoff

The corrected Definition 2.17(4c) tests EXACT weak induced vertex sets.
An alternative to the still-unproved closed-U-rank increment must
separate low-intrinsic-rank weak tests (already completable by the
previous closed-hull invariant) from high-intrinsic-rank tests.

For any exact weak structure F with at most j+1 vertices:

* If USize(F) <= j, the previous closed rank-j invariant in the
  U-closed ambient structure completes F via its ambient U-hull.
  The new strict-drop-safe bound USize(cl_ambient(F)) <= USize(F)
  is used here; there is no FALSE rank equality.
* Otherwise |F|=j+1 and USize(F)=|F|. By the checked maximal-rank
  theorem, EVERY induced subset is relatively U-closed inside F.
  This leaves an explicitly closure-independent exact weak
  test for the genuine Hales--Jewett history/decomposition argument.

No hypothesis about global K-membership of F, its intrinsic
U-closedness, or the number of vertices of its ambient hull is made.
This is an exact source-size dichotomy, NOT yet a proof that the
maximal-rank branch can be completed in arbitrary Picture histories.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Intrinsic weak U-rank is either at most j, or a finite source
with at most j+1 vertices has EXACTLY j+1 vertices, maximal rank,
and ALL of its subsets are relatively U-closed.

The ambient U-closedness and any completion hypothesis are absent
from this purely finite structural dichotomy. -/
theorem weak_rank_le_or_maximal_independent
    [Fintype V]
    (rules : ClosureDescription L) (F : RelStructure L V)
    (j : ℕ) (hCard : Fintype.card V ≤ j + 1) :
    USize rules F ≤ j ∨
      (Fintype.card V = j + 1 ∧
        USize rules F = Fintype.card V ∧
        ∀ S : Set V, IsUSubstructure rules F S) := by
  classical
  by_cases hLow : USize rules F ≤ j
  · exact Or.inl hLow
  · right
    have hBound : USize rules F ≤ Fintype.card V :=
      USize_le_card rules F
    have hCardEq : Fintype.card V = j + 1 := by omega
    have hMax : USize rules F = Fintype.card V := by omega
    exact ⟨hCardEq, hMax,
      all_subsets_relative_of_USize_eq_card rules F hMax⟩

/-- A finite weak test S of an ambient CLOSED C either already has a
corrected K-completion by the closed rank-j invariant, or is an
EXACT j+1-vertex maximal-U-rank structure in which EVERY subset is
relatively U-closed.

The first branch completes the ambient hull of S and pulls the map
back to the ORIGINAL weak S: it never substitutes the larger hull as
the tested vertex set. The second branch exposes the only cases that
a weak-vertex-size induction still has to handle in real Picture
histories. -/
theorem weak_test_complete_or_maximal_independent
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    [Finite V]
    (C : RelStructure L V) (hC : IsUClosed rules C)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ j →
      HasClosedUKCompletion K rules (C.induce T))
    (S : Finset V) (hCard : S.card ≤ j + 1) :
    HasClosedUKCompletion K rules (C.induce (↑S : Set V)) ∨
      (S.card = j + 1 ∧
        USize rules (C.induce (↑S : Set V)) = S.card ∧
        ∀ T : Set (↑S : Set V),
          IsUSubstructure rules (C.induce (↑S : Set V)) T) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hCardS : Fintype.card (↑S : Set V) = S.card := by simp
  rcases weak_rank_le_or_maximal_independent rules
      (C.induce (↑S : Set V)) j (by simpa [hCardS] using hCard) with
      hLow | ⟨hFull, hMax, hRelative⟩
  · left
    let H : Set V := UClosureHull rules C (↑S : Set V)
    letI : Fintype H := Fintype.ofFinite H
    have hHull : IsUClosed rules (C.induce H) :=
      hC.induce_UClosureHull (↑S : Set V)
    have hHullRank : USize rules (C.induce H) ≤ j :=
      (USize_induce_ambient_hull_le_weak rules C
        (↑S : Set V)).trans hLow
    have hCompletion : HasClosedUKCompletion K rules (C.induce H) :=
      hRank H hHull hHullRank
    let e : Embedding (C.induce (↑S : Set V)) (C.induce H) := {
      toFun := fun x =>
        ⟨x.1, subset_UClosureHull rules C (↑S : Set V) x.2⟩
      injective := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : H => z.1) h
      map_rel_iff := fun _ _ => Iff.rfl
    }
    exact hCompletion.pullback_embedding e
  · right
    exact ⟨by simpa [hCardS] using hFull,
      by simpa [hCardS] using hMax, hRelative⟩

end StructuralRamsey.RelStructure

import PartiteConstruction.Ramsey.ClosureUnrestrictedRamseyPass
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-! # The unrestricted cutoff-one case of the repaired theorem

With the finite initial repair now validated over ARBITRARY nonclosed
controls, the corrected local-finiteness axiom at cutoff n <= 1 yields
a genuine K-Ramsey conclusion with no extra relative-A-copy,
closed-control, or A-embeds-in-B assumption.

The proof constructs the actual U-closed global Ramsey witness C over
D by the new unrestricted Picture pass. Every closed U-irreducible test
of C embeds in the fixed B in K, so it has a K-completion. Since every
closed test of U-size at most one is U-irreducible, this supplies all
rank-one completions including rank zero. The existing closed-hull
restriction theorem recovers completions of ALL original weak tests of
at most n vertices. Apply the original cutoff n(B,D) unchanged.

The higher-rank increment remains open; this theorem neither assumes
nor proves any bound for rank greater than one.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V P : Type v}

/-- A fully constructed, unrestricted Ramsey conclusion inside K when
the repaired local-finiteness cutoff is at most one, even with an
arbitrary NONCLOSED original D. The starting Ramsey witness and all
intermediate Picture refinements are constructed, never postulated. -/
theorem ramsey_of_closedLocalCompletion_cutoff_one_unrestricted
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V)
    (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBIrr : B.Irreducible) (hKB : K B)
    (hD : D.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (n : ℕ) (hn : n ≤ 1)
    (hLocal : ClosedULocalCompletionAt K rules B D n)
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color) :
    ∃ (Y : Type v) (_ : Finite Y)
      (Target : RelStructure L Y),
      K Target ∧ StructuralRamsey.Arrow A B Target Color := by
  obtain ⟨Y, hY, C, hRamsey, hC, hPart, hCover⟩ :=
    closed_ramsey_unrestricted A B D hA hB Color hArrow
  letI : Finite Y := hY
  apply ramsey_of_closedLocalCompletionAt_rank_and_coverage
    A B D C.toRelStructure n Color
    hLocal hHer hKB hC hD C.part hPart hCover ?_ hRamsey
  intro S hS hClosed hRank
  exact closed_rank_one_completions_of_protected_coverage
    hKB hBIrr hCover S hClosed (hRank.trans hn)

end StructuralRamsey.Partite.Induced

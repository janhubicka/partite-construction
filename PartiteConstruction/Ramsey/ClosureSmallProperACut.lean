import PartiteConstruction.Ramsey.ClosureWeakProjectedRankGlue
import PartiteConstruction.Ramsey.ClosureMaximalWeakRank
import PartiteConstruction.Relational.FreeAmalgamationClass

/-!
# Proper weak free cuts with a projected closed A-boundary

The repaired rank j->j+1 proof need not charge the separator
generators twice if the TEST being completed has at most j+1
VERTICES. After a mixed proper free cut, each source side has
strictly fewer vertices and hence at most j vertices. Its
ENTIRE image under the existing protected projection to the
old U-closed control D therefore has a support of <=j vertices,
so its closure in D has U-size <=j. This support ALREADY
includes the projected source separator. The closed hull of
the separator lies in a fixed embedded A∈K, giving a common
closed K-boundary Q to glue the two independent completions.

This is an ACTUAL small-weak-cardinality analogue of earlier
conditional projected-rank gluing. It DOES NOT assert side
U-sizes drop relative to USize of Whole, and does not assume
the source separator is intrinsically U-closed or belongs to K.
The only history condition is that the separator's projection
lies inside ONE selected closed A-copy in the ORIGINAL D.

Applied to maximal intrinsic U-rank weak tests, every source
subset is relatively U-closed (merged PR #211), so the two
side-range hypotheses are automatic. The remaining task in
the actual HJ Picture stage is to construct the proper mixed
free cut whose separator maps into its selected A-copy.

This lemma proves the displayed conditional step without
an oracle for a shared target completion or generator rank.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V C : Type v}

/-- An EXACT weak source F of <=j+1 vertices, with a PROPER free
decomposition whose ranges are relatively U-closed and whose
separator projects into a closed K-copy A in an old U-closed D,
inherits a corrected K-completion from the old rank-j invariant.
No intrinsic closedness of F or either side is assumed. -/
theorem HasClosedUKCompletion.of_small_proper_projected_A_cut
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L U} {D : RelStructure L V}
    {F : RelStructure L C}
    [Finite C] [Finite V] [DecidableEq V]
    (hK : HasFiniteStrongAmalgamation K)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {B : RelStructure L Y},
      K B → IsUClosed rules E → Embedding E B → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X),
      K E → E.Irreducible)
    (hKA : K A) (hA : IsUClosed rules A)
    (hD : IsUClosed rules D) (a : Embedding A D)
    (p : C → V)
    (hp : IsClosedUHomomorphismEmbedding rules F D p)
    (j : ℕ) (hCard : Nat.card C ≤ j + 1)
    (d : ProperFreeDecomposition F)
    (hRelL : IsUSubstructure rules F (Set.range d.leftIn))
    (hRelR : IsUSubstructure rules F (Set.range d.rightIn))
    (hSep : ∀ r : d.Common,
      p (d.leftIn (d.toLeft r)) ∈ Set.range a)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules F := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hSmallL : Fintype.card d.Left ≤ j := by
    have hlt : Fintype.card d.Left < Fintype.card C :=
      Fintype.card_lt_of_injective_not_surjective
        d.leftIn d.leftIn.injective d.leftProper
    have hnat : Fintype.card C = Nat.card C :=
      (Nat.card_eq_fintype_card).symm
    omega
  have hSmallR : Fintype.card d.Right ≤ j := by
    have hlt : Fintype.card d.Right < Fintype.card C :=
      Fintype.card_lt_of_injective_not_surjective
        d.rightIn d.rightIn.injective d.rightProper
    have hnat : Fintype.card C = Nat.card C :=
      (Nat.card_eq_fintype_card).symm
    omega
  let JL : Finset V := (Finset.univ : Finset d.Left).image
    (p ∘ d.leftIn)
  let JR : Finset V := (Finset.univ : Finset d.Right).image
    (p ∘ d.rightIn)
  have hJL : JL.card ≤ j := by
    calc
      JL.card ≤ (Finset.univ : Finset d.Left).card :=
        Finset.card_image_le
      _ = Fintype.card d.Left := Finset.card_univ
      _ ≤ j := hSmallL
  have hJR : JR.card ≤ j := by
    calc
      JR.card ≤ (Finset.univ : Finset d.Right).card :=
        Finset.card_image_le
      _ = Fintype.card d.Right := Finset.card_univ
      _ ≤ j := hSmallR
  have hRangeL (x : d.Left) :
      p (d.leftIn x) ∈
        UClosureHull rules D (↑JL : Set V) := by
    apply subset_UClosureHull rules D (↑JL : Set V)
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_univ x, rfl⟩
  have hRangeR (x : d.Right) :
      p (d.rightIn x) ∈
        UClosureHull rules D (↑JR : Set V) := by
    apply subset_UClosureHull rules D (↑JR : Set V)
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_univ x, rfl⟩
  exact HasClosedUKCompletion.of_common_projection_supports_relative
    rules hK hHereditary hKIrr
    d.free hRelL hRelR
    hKA hA hD a p hp hSep
    JL JR j hJL hJR hRangeL hRangeR hRank

/-- For MAXIMAL-U-RANK weak tests, every side range of ANY proper
free decomposition is relatively U-closed automatically. The only
remaining geometric input needed by the small-proper-cut completion
criterion is that the separator projects into a single closed
A-copy in D. No completion of the possibly nonclosed source root
is separately required. -/
theorem HasClosedUKCompletion.of_maximal_weak_projected_A_cut
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L U} {D : RelStructure L V}
    {F : RelStructure L C}
    [Fintype C] [Finite V] [DecidableEq V]
    (hK : HasFiniteStrongAmalgamation K)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {B : RelStructure L Y},
      K B → IsUClosed rules E → Embedding E B → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X),
      K E → E.Irreducible)
    (hKA : K A) (hA : IsUClosed rules A)
    (hD : IsUClosed rules D) (a : Embedding A D)
    (p : C → V)
    (hp : IsClosedUHomomorphismEmbedding rules F D p)
    (j : ℕ) (hCard : Fintype.card C ≤ j + 1)
    (hMax : USize rules F = Fintype.card C)
    (d : ProperFreeDecomposition F)
    (hSep : ∀ r : d.Common,
      p (d.leftIn (d.toLeft r)) ∈ Set.range a)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules F := by
  have hAll := all_subsets_relative_of_USize_eq_card rules F hMax
  have hCard' : Nat.card C ≤ j + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hCard
  exact HasClosedUKCompletion.of_small_proper_projected_A_cut
    hK hHereditary hKIrr hKA hA hD a p hp
    j hCard' d (hAll (Set.range d.leftIn))
    (hAll (Set.range d.rightIn)) hSep hRank

end StructuralRamsey.RelStructure

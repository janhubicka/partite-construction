import PartiteConstruction.Ramsey.ClosureMaximalWeakRank
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank
import PartiteConstruction.Ramsey.ClosureProjectedGenerators

/-!
# Maximal-rank exact weak tests: ordinary maps preserve completions

An ordinary relational homomorphism-embedding need not protect
closed U-irreducible tests of an arbitrary weak source. For a finite
source of MAXIMAL intrinsic U-rank, however, every subset is
relatively U-closed and every embedded closed U-irreducible test is
ordinarily irreducible (#211). Thus an ordinary homomorphism-
embedding becomes a protected closed-test map without any closedness
assumption on the source or its target.

If the source has at most n vertices, its entire image contains
at most n vertices. Whenever the old target has corrected
K-completions for ALL exact weak induced subsets of at most n
vertices, the induced weak image has such a completion, which
pulls back along the protected map.

This is a useful transfer lemma for the coordinate retractions
of the actual non-semi-closed native Hales--Jewett subattachments:
it requires only the previous WEAK-vertex-size invariant,
not a rank inequality for any closed source hull. It does NOT
assert that the whole Hales--Jewett attachment has one coordinate
retraction or resolve the multi-line branch with no common
variable coordinate.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V : Type v}

/-- On a finite weak source of maximal intrinsic U-rank, any
ordinary homomorphism-embedding into Old inherits a corrected
K-completion from the previous weak n-vertex completion
invariant of Old. The source itself need not be U-closed and
no assumption that f is globally injective is introduced. -/
theorem HasClosedUKCompletion.of_maximal_rank_ordinaryHE_weakImage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {Old : RelStructure L V}
    [Fintype U] [Fintype V]
    (f : U → V)
    (hf : Source.IsHomomorphismEmbedding Old f)
    (hMax : USize rules Source = Fintype.card U)
    (n : ℕ)
    (hCard : Fintype.card U ≤ n)
    (hOldWeak : ∀ S : Finset V, S.card ≤ n →
      HasClosedUKCompletion K rules (Old.induce (↑S : Set V))) :
    HasClosedUKCompletion K rules Source := by
  classical
  let S : Finset V := Finset.univ.image f
  have hRange (x : U) : f x ∈ (↑S : Set V) := by
    change f x ∈ S
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hImageCard : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset U).card := Finset.card_image_le
      _ = Fintype.card U := Finset.card_univ
      _ ≤ n := hCard
  have hImageCompletion :
      HasClosedUKCompletion K rules (Old.induce (↑S : Set V)) :=
    hOldWeak S hImageCard
  have hProtected : IsClosedUHomomorphismEmbedding rules Source Old f :=
    hf.toClosedMap_of_max_USize hMax
  exact hImageCompletion.precomp_closedMap
    (hProtected.codRestrict (↑S : Set V) hRange)


/-- In particular the older CLOSED-rank-n completion invariant of Old
implies the weak-n-vertex completion hypothesis required above, by
completing the ambient hull of each exact weak image and restricting
the same completion map back to its original vertex carrier. This
requires Old to be U-closed, but not the source of the ordinary HE. -/
theorem HasClosedUKCompletion.of_maximal_rank_ordinaryHE_closedRank
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {Old : RelStructure L V}
    [Fintype U] [Finite V]
    (hOldClosed : IsUClosed rules Old)
    (f : U → V)
    (hf : Source.IsHomomorphismEmbedding Old f)
    (hMax : USize rules Source = Fintype.card U)
    (n : ℕ)
    (hCard : Fintype.card U ≤ n)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.induce T) →
      USize rules (Old.induce T) ≤ n →
        HasClosedUKCompletion K rules (Old.induce T)) :
    HasClosedUKCompletion K rules Source := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply HasClosedUKCompletion.of_maximal_rank_ordinaryHE_weakImage
    (rules := rules) (K := K) f hf hMax n hCard
  intro S hS
  exact HasClosedUKCompletion.of_closed_USize
    rules Old hOldClosed n hOldRank S hS

end StructuralRamsey.RelStructure

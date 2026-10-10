import PartiteConstruction.Ramsey.ClosureLineSubfamilyWeakRetraction
import PartiteConstruction.Ramsey.ClosureMaximalWeakImageTransfer

/-!
# Completion of maximal weak tests on a true common-coordinate subattachment

The native Hales--Jewett little Picture can be non-semi-closed because
different attached old copies give conflicting closure outputs. This
statement does NOT assume closure or semi-closedness of the attachment,
or relative U-closedness of the old attaching support.

If a selected family of its genuine canonical lines shares one
parameter coordinate k, evaluate the entire attached picture at k.
The checked native fold lemma constructs an ORDINARY relational
homomorphism-embedding into Old. Given any exact finite weak test F
embedded in this subattachment with USize(F)=|F| and |F|<=n, its
induced weak image in Old is on at most n vertices. When Old has
corrected K-completions of ALL exact weak n-vertex tests, F obtains
a corrected completion by the maximal-weak-rank ordinary-HE transfer.

This closes the pure-core/common-coordinate-subfamily branch of the
exact-weak-size increment, assuming the previous stage's weak
completion invariant. It requires no single coordinate shared by
the FULL Hales--Jewett Ramsey line family, which is generally false.
The genuinely transverse multi-line branch still needs a common
closed K-boundary for its separate coordinate projections.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree
universe u v
variable {L : RelLanguage.{u}}
variable {P Q V I X : Type v} {N : ℕ}

/-- A maximal-U-rank exact weak source embedded in an ACTUAL native
subattachment, with one parameter coordinate common to its
selected lines, has a corrected K-completion from all small weak
completions of Old. The total subattachment need NOT be U-closed
or semi-closed. No target root-closedness, source hull-size
bound, or common parameter for unselected lines is assumed. -/
theorem completion_of_maximal_weak_common_coordinate_subattachment
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P)
    (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (k : Fin N)
    (hVariable : ∀ i : I, (lines i).symbol k = .parameter)
    [Fintype X] [Fintype V]
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (hMax : USize rules Test = Fintype.card X)
    (n : ℕ) (hCard : Fintype.card X ≤ n)
    (hOldWeak : ∀ S : Finset V, S.card ≤ n →
      HasClosedUKCompletion K rules
        (Old.toRelStructure.induce (↑S : Set V))) :
    HasClosedUKCompletion K rules Test := by
  let F := RelStructure.Attachment.attach Old.toRelStructure
    (Old.support alpha) (power (Old.restrict alpha) N).toRelStructure
    (closureLineMaps Old alpha A hRestricted lines)
  let rho : F → V :=
    RelStructure.Attachment.fold
      (fun z : Vertex (Old.restrict alpha) N => (z.coord k).1)
      (fun _ : I => id)
  have hRho : F.IsHomomorphismEmbedding Old.toRelStructure rho :=
    line_subfamily_coordinate_homomorphismEmbedding
      Old alpha A hRestricted lines k hVariable
  have hTestOld : Test.IsHomomorphismEmbedding Old.toRelStructure
      (rho ∘ e) := hRho.comp e.isHomomorphismEmbedding
  exact HasClosedUKCompletion.of_maximal_rank_ordinaryHE_weakImage
    (rules := rules) (K := K) (Old := Old.toRelStructure)
    (f := rho ∘ e) hTestOld hMax n hCard hOldWeak

end StructuralRamsey.Partite.Induced

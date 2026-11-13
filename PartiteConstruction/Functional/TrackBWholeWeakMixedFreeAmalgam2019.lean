import PartiteConstruction.Functional.TrackBOneWayWeakMapNaturality2019
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam

/-!
# Track B: exact mixed weak cuts of genuine native free amalgams

The previously verified native function-language free amalgam induces
a full genuine Option(Set) free amalgam on EVERY exact whole-fibre
weak test S, with its precise side and common-root inverse-image
carriers. The full partial side maps compose with the universally
valid source-defined whole→clipped identity on the SAME S.

Thus a single ACTUAL native free-amalgam test carries both:
* a FULL genuine partial free-amalgam decomposition of the whole weak
  test, including the exact (possibly nonclosed) common root; and
* original-2019 source-defined maps from its whole weak sides to
  the CLIPPED native weak test on the same original vertex carrier S.

These maps do not reflect undefined domains of the clipped target,
and nothing constructs a strict functional target B-tree or
H-valued ambient-relative completion of an arbitrary mixed test.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}}

/-- A full native free amalgam's exact mixed test admits a FULL
genuine partial whole-fibre free-amalgam decomposition, while BOTH
side maps to the literal clipped weak test are source-defined
original-2019 homomorphisms on their actual restricted vertex maps.

No ambient closure hull, root isolation, target completion, or
domain reflection by these two side-to-clipped maps is assumed. -/
theorem IsFreeAmalgam.wholeWeakPartial_withClippedSideMaps
    {H E F C : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.toFun ∘ sL.toFun) ⁻¹' S
    ∃ (mL : PartialSetStructure.Embedding
          (wholeWeakInduce Root.toNonemptyPartial Mset)
          (wholeWeakInduce Left.toNonemptyPartial Lset))
      (mR : PartialSetStructure.Embedding
          (wholeWeakInduce Root.toNonemptyPartial Mset)
          (wholeWeakInduce Right.toNonemptyPartial Rset))
      (jL : PartialSetStructure.Embedding
          (wholeWeakInduce Left.toNonemptyPartial Lset)
          (wholeWeakInduce Whole.toNonemptyPartial S))
      (jR : PartialSetStructure.Embedding
          (wholeWeakInduce Right.toNonemptyPartial Rset)
          (wholeWeakInduce Whole.toNonemptyPartial S)),
      PartialSetStructure.IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL.toFun a).1 = iL a.1) ∧
      (∀ b : Rset, (jR.toFun b).1 = iR b.1) ∧
      IsOriginalPartialHomomorphism
        (wholeWeakInduce Left.toNonemptyPartial Lset)
        (weakInduce Whole.toNonemptyPartial S) jL.toFun ∧
      IsOriginalPartialHomomorphism
        (wholeWeakInduce Right.toNonemptyPartial Rset)
        (weakInduce Whole.toNonemptyPartial S) jR.toFun := by
  obtain ⟨mL, mR, jL, jR, hFreeWhole, hLeft, hRight⟩ :=
    hFree.wholeWeakPartialInduce_withMaps S
  refine ⟨mL, mR, jL, jR, hFreeWhole, hLeft, hRight, ?_, ?_⟩
  · exact (wholeWeakInduce_to_clipped_originalPartial
      Whole.toNonemptyPartial S).comp jL.toOriginalPartialHom
  · exact (wholeWeakInduce_to_clipped_originalPartial
      Whole.toNonemptyPartial S).comp jR.toOriginalPartialHom

end StructuralRamsey.Structure

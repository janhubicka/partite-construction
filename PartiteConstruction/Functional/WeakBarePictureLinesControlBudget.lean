import PartiteConstruction.Functional.WeakBareNativeUnitAttachmentBudget
import PartiteConstruction.Functional.EHNLineOnlyPicture
import PartiteConstruction.Functional.WeakHistoryFreeTreeBasePower

/-!
# Track D: full native finite genuine HJ-line Picture with BARE rank budget

English proof FIRST:
docs/track-d-english-finite-HJ-bare-picture-budget-20261114.md

Unlike a common-coordinate HJ line subfamily, the verified
`pictureLemma_lines_preservingSupport` attaches the FULL finite
family of genuine Hales–Jewett lines needed for the Ramsey arrow.
It already carries any stage predicate stable under a TRUE native
binary full-functional selected-support attachment.

For the deliberately weaker BARE exact weak strict full-functional
B-tree invariant:
- the TRUE power core gets one-copy witnesses via EHN↪Base;
- the already checked actual UnitAttachD bare rank successor
  (stacked PR #685) supplies stable binary attachment, provided
  the ORIGINAL fixed control has independently paid the explicit
  finite A-trace rank budget F_A(m).

Thus the finite HJ Picture itself has the ordinary coloring
PictureProperty AND BARE strict functional rank m+1.
The control's bigger rank, outer arrow/rank schedule,
initial nullary root and final 2019 partial arrow / B coverage
are separate mathematical obligations, not hidden here.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P U VB : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual FINITE UNRESTRICTED Hales–Jewett LINE Picture
preserves strict BARE functional weak-tree locality rank m+1
if the old full-functional Stage already has that rank and
the fixed genuine original EHN control D has the independently
paid A-trace restoration rank F_A(m).

All copied stages stay inside the genuine hereditary
free-amalgamation class K. Both target-tree locality and
the ordinary functional `PictureProperty` are returned.

No common line parameter coordinate, arbitrary history diary,
protected unoccupied target A mark, global target retraction,
root injectivity, or closure of weak tested source sets
is required. This does NOT yet construct the control
with the larger BARE rank or prove outer n-pass sparsening. -/
theorem pictureLemma_lines_preservingBareRank_of_controlBudget
    [Finite P] [Finite U] 
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (hA : A.Irreducible) (hKA : K A)
    (Base : Structure L VB) (hBase : Base.Irreducible)
    (eAB : Structure.Embedding A Base)
    (Old : Stage K D)
    (alpha : Structure.Embedding A D)
    (m : ℕ)
    (hOldBare :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base Old.system.toStructure (m + 1))
    (hControlBare :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base D
        (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := U) m))
    (κ : Type*) [Fintype κ] :
    ∃ New : Stage K D,
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base New.system.toStructure (m + 1) ∧
      PictureProperty A Old New alpha κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    SetAmbientRelativeWeakTreeWitness.AtMostBare
      Base T.system.toStructure (m + 1)
  change ∃ New : Stage K D, Q New ∧
    PictureProperty A Old New alpha κ
  apply pictureLemma_lines_preservingSupport
    hK A hKA Old alpha κ Q
  · intro N hN
    dsimp only
    let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
    have hR : R.WeaklyPartiteOver A :=
      Old.system.weakRestrict_invariant
        D Old.isPartite.1 A alpha Old.isPartite
    let E := Induced.power R N
    have hPower : E.WeaklyPartiteOver A :=
      Induced.power_weaklyPartiteOver hR hN
    have hBareE :
        SetAmbientRelativeWeakTreeWitness.AtMostBare
          Base E.toStructure (m + 1) := by
      intro S _hS
      obtain ⟨Y, Target, hTree, f, hWeak, _hCopies, _hHist⟩ :=
        SetAmbientRelativeWeakTreeWitness.of_ehn_oneCopy_noHistory
          hA hBase eAB hPower
          (id : Induced.Vertex R N → Induced.Vertex R N)
          (↑S : Set (Induced.Vertex R N))
      exact ⟨Y, Target, hTree, f, hWeak⟩
    simpa only [Q] using hBareE
  · intro T f hQT
    change
      SetAmbientRelativeWeakTreeWitness.AtMostBare Base
        (Attachment.UnitAttachD Old.system
          (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed
            D Old.isPartite.1 A alpha)
          T.system f).toStructure (m + 1)
    exact Attachment.UnitAttachD_bareRank_of_controlBudget
      Old.system D Old.isPartite A hA alpha
      T.system T.isPartite f Base m
      hQT hOldBare hControlBare

end StructuralRamsey.FunctionalPartite.EHN

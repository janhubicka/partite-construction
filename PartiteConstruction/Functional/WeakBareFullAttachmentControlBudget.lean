import PartiteConstruction.Functional.WeakBarePureSideTransfer
import PartiteConstruction.Functional.WeakHistoryFreeMixedRankStep

/-!
# Track D: true native FULL functional free-cut BARE strict rank successor

English proof FIRST:
docs/track-d-english-bare-full-attachment-budget-20261114.md

On a genuine FULL functional source free amalgam, the strict BARE
ambient-relative weak-tree property is preserved at rank m+1 when:
- BOTH entire source sides retain BARE strict tree rank m+1;
- the common true EHN control D has BARE rank
    m + (m+1)^|A| * |A|;
- the common source root maps into one FULL selected A↪D and
  A is irreducible.

PURE tested sets transfer bare weak HEs from the corresponding
full source side without requiring ANY external partial A-trace
protection. MIXED exact weak tests use the verified rank-m control
A-trace restoration and exact mixed #642 successor, forgetting
the external ambient A-certificate afterward.

This is the first abstract FULL binary functional attachment
rank step for a genuinely weaker induction invariant. The
larger fixed CONTROL rank requirement must still be supplied
noncircularly in the outer Picture iteration. No n-pass theorem
is claimed by this lemma alone, and the frozen survey is untouched.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- BARE native strict functional local-tree rank-(m+1)
successor for one REAL full source free-amalgam cut, with the
external control's finite labeled-A-trace restoration budget
paid explicitly, not hidden in the exact weak tested source size.

The source common root can be reducible, arbitrarily generated
and have colliding canonical EHN parts. Both projected side
sets may be nonclosed, and all function output fibres may be
genuinely multivalued. Source-undefined inputs impose no
target-domain reflection.

This is NOT arbitrary-history/ProtectedAMark preservation and
NOT the full ordered HJ Picture iteration; those remain separate.
-/
theorem AtMostBare_of_control_budget_mixed_full_cut
    {A : Structure L UA} (hA : A.Irreducible)
    [Fintype UA] [Fintype P]
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype E] [Fintype F] [DecidableEq C] [DecidableEq P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (p : C → P)
    (hp : Whole.IsEHNHomomorphismEmbedding D p)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, p (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (m : ℕ)
    (hBareL :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base Left (m + 1))
    (hBareR :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base Right (m + 1))
    (hBareD :
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base D
        (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := UA) m)) :
    SetAmbientRelativeWeakTreeWitness.AtMostBare
      Base Whole (m + 1) := by
  classical
  have hPrev :
      SetAmbientRelativeWeakTreeWitness.AtMostNoHistory
        A Base D (id : P → P) m :=
    SetAmbientRelativeWeakTreeWitness.AtMostBare.restore_full_ambient_A_traces
      hA m hBareD (id : P → P)
  intro S hS
  by_cases hOutsideL :
      ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e
  · by_cases hOutsideR :
        ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f
    · obtain ⟨Y, Target, hTree, f, hWeak, _hCopies, _hHist⟩ :=
        hSrc.noHistory_weakRankSucc_mixed
          hA D alpha p hp hRootAlpha Base m hPrev
          S hS hOutsideL hOutsideR
      exact ⟨Y, Target, hTree, f, hWeak⟩
    · have hPureR : ∀ z : C, z ∈ S → ∃ f : F, z = iR f := by
        intro z hz
        by_contra hzNo
        apply hOutsideR
        exact ⟨z, hz, by
          intro f hEq
          exact hzNo ⟨f, hEq⟩⟩
      exact hBareR.pure_side_of_full_embedding iR (m + 1)
        S hS hPureR
  · have hPureL : ∀ z : C, z ∈ S → ∃ e : E, z = iL e := by
      intro z hz
      by_contra hzNo
      apply hOutsideL
      exact ⟨z, hz, by
        intro e hEq
        exact hzNo ⟨e, hEq⟩⟩
    exact hBareL.pure_side_of_full_embedding iL (m + 1)
      S hS hPureL

end StructuralRamsey.Structure.IsFreeAmalgam

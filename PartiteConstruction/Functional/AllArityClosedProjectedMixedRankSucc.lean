import PartiteConstruction.Functional.MixedProjectedSideBudgets
import PartiteConstruction.Functional.ProtectedProjectedSideMixedGlue
import PartiteConstruction.Functional.ClosedControlStrictPredecessor

/-!
# All-arity strict native functional mixed successor with CLOSED projected sides

A genuine FULL functional free attachment Whole=Left *Root Right
has an EHN/original-2019 projection p:Whole→D and a selected
FULL alpha:A↪D containing the projected attaching root.
Fix any EXACT finite weak source S with |S|≤m+1 that is
genuinely mixed: each side embedding omits a tested point.

The two LITERAL projected side images I_L,I_R automatically
have at most m vertices, independently of projection injectivity.
Assume only that these TWO SPECIFIC image subsets are
function-CLOSED in the functional control D. The original
source weak S need not be closed, and p need not be globally
FULL or domain-reflecting.

The WEAKER rank-m closed-control-only strict history
predecessor \`AtMostClosed(A,Base,D,m)\` now yields genuine
STRICT full-functional protected alpha marks on both exact
projected side tests. The previously checked protected
projected-side EHN pullback / FULL target A-mark gluing
gives a STRICT full-functional Base-tree witness of S
with all surviving multivalued function fibres, actual
full ambient A-copy intersections and projected histories.

This theorem works with arbitrary function arities, including
nullaries and repeated inputs. It deliberately leaves the
nonclosed projected-side image case unresolved; a test-local
absence of EHN phantom domains is one sufficient condition
to discharge these closedness hypotheses (proved separately).
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- A genuinely mixed exact weak source test of ≤m+1 vertices
inherits a strict FULL-functional Base-tree history witness
from the WEAKER rank-m closed-control-only predecessor,
provided its two literal projected side images in D are
function-closed.

No closedness assumption on S or global total-fibre EHN map.
All gluing is over FULL protected TARGET A-copies. -/
theorem weakTree_of_closedProjected_alpha_mixed_succ
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype UA] [Fintype P] [DecidableEq P] [DecidableEq C]
    [Fintype E] [Fintype F]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (p : C → P)
    (hp : Whole.IsEHNHomomorphismEmbedding D p)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, p (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (eAB : Embedding A Base) (hBase : Base.Irreducible)
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMostClosed
      A Base D m)
    (S : Finset C) (hS : S.card ≤ m + 1)
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
    (hProjectedClosedL : D.IsClosed
      ((↑(Finset.image (p ∘ iL)
        ((Finset.univ : Finset E).filter (fun e => iL e ∈ S)))) : Set P))
    (hProjectedClosedR : D.IsClosed
      ((↑(Finset.image (p ∘ iR)
        ((Finset.univ : Finset F).filter (fun f => iR f ∈ S)))) : Set P))
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) history := by
  classical
  let pL : E → P := p ∘ iL
  let pR : F → P := p ∘ iR
  let SL : Finset E := Finset.univ.filter (fun e => iL e ∈ S)
  let SR : Finset F := Finset.univ.filter (fun f => iR f ∈ S)
  let IL : Finset P := SL.image pL
  let IR : Finset P := SR.image pR
  have hImgL :
      (↑IL : Set P) = pL '' (iL ⁻¹' (↑S : Set C)) := by
    have hSL : (↑SL : Set E) = iL ⁻¹' (↑S : Set C) := by
      ext x
      simp [SL]
    rw [← hSL]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hImgR :
      (↑IR : Set P) = pR '' (iR ⁻¹' (↑S : Set C)) := by
    have hSR : (↑SR : Set F) = iR ⁻¹' (↑S : Set C) := by
      ext x
      simp [SR]
    rw [← hSR]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hBudget :=
    StructuralRamsey.Structure.projectedSideBudgets_of_mixed
      iL iR p m S hS hMixedL hMixedR
  have hCardL : IL.card ≤ m := hBudget.1
  have hCardR : IR.card ≤ m := hBudget.2
  have hControlL : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P) (↑IL : Set P) history :=
    hPrev.protected_of_closedOccupiedA
      eAB hBase alpha IL hCardL hProjectedClosedL history
  have hControlR : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P) (↑IR : Set P) history :=
    hPrev.protected_of_closedOccupiedA
      eAB hBase alpha IR hCardR hProjectedClosedR history
  have hTargetL : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P)
      ((p ∘ iL) '' (iL ⁻¹' (↑S : Set C))) history := by
    rw [← hImgL]
    exact hControlL
  have hTargetR : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P)
      ((p ∘ iR) '' (iR ⁻¹' (↑S : Set C))) history := by
    rw [← hImgR]
    exact hControlR
  exact hSrc.weakTree_of_protected_projected_side_witnesses
    hA D alpha p hp hRootAlpha Base
    (↑S : Set C) history hTargetL hTargetR

end StructuralRamsey.Structure.IsFreeAmalgam

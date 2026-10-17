import PartiteConstruction.Functional.BudgetedAlphaWeakWitness
import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue

/-!
# Actual strict functional mixed gluing from BUDGETED predecessor boundaries

Let Whole be a genuine full functional free amalgam of Left and Right
over Root, with a global EHN source-defined partial projection
p:Whole→D. The full attaching root projects into one full
alpha:A↪D. Fix an exact weak tested finite vertex set S.

The two side projections I_L,I_R are exact set-theoretic images of
their literal intersections with S. Rather than assuming the FALSE
universal full protected-alpha predecessor property, use only the
verified ORDINARY rank-m weak-tree history invariant on D, and check
that BOTH explicit unions I_L∪alpha[A], I_R∪alpha[A] have ≤m
vertices.

The budgeted predecessor lemma gives a strict functional Base-tree
with a full protected alpha mark on each exact projected side;
EHN pullback supplies the exact original source weak side maps.
Our checked protected FULL-A gluing then combines the two target
trees, retaining arbitrary multivalued outputs, all genuine full
ambient-A-copy intersections, and all finite projected histories.

This is a positive, non-tautological special case of the repaired
functional Appendix A n-vertex rank step, and can be invoked with
m=n−1. It neither enlarges the source S nor takes any function
closure. The remaining hard cases are precisely where one of the
missing selected-alpha boundaries is UNAFFORDABLE in rank m.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- A full FUNCTIONAL source free attachment has an exact strict
weak B-tree witness as soon as the two projected side tests, after
adding the missing selected alpha(A) vertices, BOTH fit the
ORDINARY predecessor's exact weak-test vertex budget m.

No false global protected-mark invariant, unconditional arbitrary
mixed-root extension, singleton-valuedness, or total-fibre
homomorphism is postulated. -/
theorem weakTree_of_budgeted_alpha_sides
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
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (S : Finset C)
    (hBudgetL :
      ((((Finset.univ : Finset E).filter (fun e => iL e ∈ S))
          .image (p ∘ iL)) ∪
        ((Finset.univ : Finset UA).image alpha)).card ≤ m)
    (hBudgetR :
      ((((Finset.univ : Finset F).filter (fun z => iR z ∈ S))
          .image (p ∘ iR)) ∪
        ((Finset.univ : Finset UA).image alpha)).card ≤ m)
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) history := by
  classical
  let pL : E → P := p ∘ iL
  let pR : F → P := p ∘ iR
  let SL : Finset E := Finset.univ.filter (fun e => iL e ∈ S)
  let SR : Finset F := Finset.univ.filter (fun z => iR z ∈ S)
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
  have hpL : Left.IsEHNHomomorphismEmbedding D pL :=
    hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : Right.IsEHNHomomorphismEmbedding D pR :=
    hp.comp iR.isEHNHomomorphismEmbedding
  have hControlL : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P) (↑IL : Set P) history :=
    hPrev.protected_of_union_budget IL alpha hBudgetL history
  have hControlR : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P) (↑IR : Set P) history :=
    hPrev.protected_of_union_budget IR alpha hBudgetR history
  have hTargetL : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P)
      (pL '' (iL ⁻¹' (↑S : Set C))) history := by
    rw [← hImgL]
    exact hControlL
  have hTargetR : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P)
      (pR '' (iR ⁻¹' (↑S : Set C))) history := by
    rw [← hImgR]
    exact hControlR
  have hLeft : SetAmbientProtectedWeakTreeWitness A Base alpha
      Left pL (iL ⁻¹' (↑S : Set C)) history :=
    SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pL (id : P → P) pL hpL
      (fun _ => rfl) hA
      (iL ⁻¹' (↑S : Set C)) history hTargetL
  have hRight : SetAmbientProtectedWeakTreeWitness A Base alpha
      Right pR (iR ⁻¹' (↑S : Set C)) history :=
    SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pR (id : P → P) pR hpR
      (fun _ => rfl) hA
      (iR ⁻¹' (↑S : Set C)) history hTargetR
  obtain ⟨ZL, TL, hTreeL, fL, hWeakL, hCopiesL, hHistL,
    markL, hcL, hTraceL⟩ := hLeft
  obtain ⟨ZR, TR, hTreeR, fR, hWeakR, hCopiesR, hHistR,
    markR, hcR, hTraceR⟩ := hRight
  exact hSrc.protectedAMarkWeakTree_glue hA
    (↑S : Set C) alpha p pL pR
    (fun _ => rfl) (fun _ => rfl)
    hRootAlpha Base TL TR hTreeL hTreeR markL markR hcL hcR
    fL fR hWeakL hWeakR hTraceL hTraceR
    hCopiesL hCopiesR history hHistL hHistR

end StructuralRamsey.Structure.IsFreeAmalgam

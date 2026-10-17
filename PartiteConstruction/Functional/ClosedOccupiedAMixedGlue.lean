import PartiteConstruction.Functional.ClosedOccupiedAPredecessor
import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue

/-!
# Strict functional mixed step with CLOSED occupied A-boundaries

This theorem follows the VERIFIED relational Appendix A mixed step in
the genuine FULL FUNCTION language. On the EXACT finite weak mixed
test, its two source sides have projected images I_L,I_R. If both
occupied selected alpha(A) sets H_L,H_R are FUNCTION-CLOSED in A,
the ordinary rank-m predecessor weak history witnesses on D produce
FULL protected target A-marks by attaching one fresh Base-copy
along the full closed partial A boundary on each side.

EHN pullback and the already checked genuine set-valued functional
A-mark free gluing then give a STRICT full-functional Base-tree
witness on the original exact weak test, preserving ambient full
A intersections and arbitrary projected histories.

For relational languages every H is automatically closed; thus this
includes the corresponding positive relational mixed gluing case.
No extra projected A vertices are charged to the cutoff m, and no
false universal protected-mark predecessor is assumed.

The remaining hard case is when one occupied partial A-boundary is
not function-closed, equivalently when some active ambient output-part
mask is missing in that weak boundary.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- A genuine FULL functional mixed attachment has a strict
full-functional Base-tree completion of an exact weak test whenever
its two exact projected side images fit the ordinary predecessor
rank m AND their occupied selected A-boundaries are function-closed.

This directly replaces the relational partial A-root extension
lemma for every closed functional partial root, with no missing-alpha
vertex budget or global protected predecessor oracle. -/
theorem weakTree_of_closedOccupied_alpha_sides
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
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (S : Finset C)
    (hCardL :
      (Finset.image (p ∘ iL)
          ((Finset.univ : Finset E).filter (fun e => iL e ∈ S))).card ≤ m)
    (hCardR :
      (Finset.image (p ∘ iR)
          ((Finset.univ : Finset F).filter (fun z => iR z ∈ S))).card ≤ m)
    (hClosedL : A.IsClosed {a : UA |
      alpha a ∈ ((↑(Finset.image (p ∘ iL)
          ((Finset.univ : Finset E).filter (fun e => iL e ∈ S)))) : Set P)})
    (hClosedR : A.IsClosed {a : UA |
      alpha a ∈ ((↑(Finset.image (p ∘ iR)
          ((Finset.univ : Finset F).filter (fun z => iR z ∈ S)))) : Set P)})
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
    hPrev.protected_of_closedOccupiedA eAB hBase alpha IL hCardL hClosedL history
  have hControlR : SetAmbientProtectedWeakTreeWitness A Base
      alpha D (id : P → P) (↑IR : Set P) history :=
    hPrev.protected_of_closedOccupiedA eAB hBase alpha IR hCardR hClosedR history
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

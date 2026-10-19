import PartiteConstruction.Functional.AllArityClosedProjectedMixedRankSucc
import PartiteConstruction.Functional.UnaryEHNCompletion
import PartiteConstruction.Structure.HomImageClosed

/-!
# Unary closed mixed functional successor from CLOSED-control-only predecessor

For a genuinely CLOSED exact mixed source S with |S|≤m+1 in an
ACTUAL FULL functional free attachment, all exact side preimages
are CLOSED. Unary EHN maps are FULL functional homomorphisms,
so the literal projected side images IL,IR are CLOSED in D.

Mixedness bounds each projected image by m using the separately
verified cardinal helper. The WEAKER rank-m AtMostClosed(A,Base,D,m)
control predecessor supplies strict full-functional protected
alpha(A) target marks on IL and IR with arbitrary projected histories.
The independently checked protected projected-side mixed gluing
now produces a STRICT full-functional Base-tree weak witness
on the ORIGINAL exact S. Closedness of S and unary function
arity upgrade the same target map to a FULL homomorphism-embedding,
not merely an original-2019 partial HE.

No artificial generated closure or counted root inflation.
The predecessor assumption does NOT quantify over all weak tests.
This proves the genuine local mixed successor for closed unary tests,
not the entire HJ finite attachment-list or n-pass theorem.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- Genuine strict mixed rank successor for function-closed unary
source tests from the WEAKER closed-control-only predecessor.
No separate occupied alpha(A)-boundary closedness assumption. -/
theorem weakTree_of_closed_unary_mixed_succ_closedPrev
    (hUnary : L.UnaryFuncArity)
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
    (hClosed : Whole.IsClosed (↑S : Set C))
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
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
  have hSetL : (↑SL : Set E) = iL ⁻¹' (↑S : Set C) := by
    ext x
    simp [SL]
  have hSetR : (↑SR : Set F) = iR ⁻¹' (↑S : Set C) := by
    ext x
    simp [SR]
  have hImgL :
      (↑IL : Set P) = pL '' (iL ⁻¹' (↑S : Set C)) := by
    rw [← hSetL]
    ext q
    constructor
    · intro hq
      obtain ⟨x, hx, hEq⟩ := Finset.mem_image.mp hq
      exact ⟨x, hx, hEq⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hImgR :
      (↑IR : Set P) = pR '' (iR ⁻¹' (↑S : Set C)) := by
    rw [← hSetR]
    ext q
    constructor
    · intro hq
      obtain ⟨x, hx, hEq⟩ := Finset.mem_image.mp hq
      exact ⟨x, hx, hEq⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hClosedSideL : Left.IsClosed (iL ⁻¹' (↑S : Set C)) :=
    iL.preimage_isClosed (↑S : Set C) hClosed
  have hClosedSideR : Right.IsClosed (iR ⁻¹' (↑S : Set C)) :=
    iR.preimage_isClosed (↑S : Set C) hClosed
  have hpL : Left.IsEHNHomomorphismEmbedding D pL :=
    hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : Right.IsEHNHomomorphismEmbedding D pR :=
    hp.comp iR.isEHNHomomorphismEmbedding
  have hFullL : Left.IsHomomorphism D pL :=
    hpL.isHomomorphism_of_unary hUnary
  have hFullR : Right.IsHomomorphism D pR :=
    hpR.isHomomorphism_of_unary hUnary
  have hIL : D.IsClosed (↑IL : Set P) := by
    rw [hImgL]
    exact hFullL.image_isClosed
      (iL ⁻¹' (↑S : Set C)) hClosedSideL
  have hIR : D.IsClosed (↑IR : Set P) := by
    rw [hImgR]
    exact hFullR.image_isClosed
      (iR ⁻¹' (↑S : Set C)) hClosedSideR
  exact hSrc.weakTree_of_closedProjected_alpha_mixed_succ
    hA D alpha p hp hRootAlpha Base eAB hBase m
    hPrev S hS hMixedL hMixedR hIL hIR history

/-- The same strict target gives a FULL unary homomorphism-embedding
of the original exact function-closed mixed test and retains actual
ambient A-copy intersections plus all projected histories. -/
theorem fullTree_of_closed_unary_mixed_succ_closedPrev
    (hUnary : L.UnaryFuncArity)
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
    (hClosed : Whole.IsClosed (↑S : Set C))
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : (↑S : Set C) → Z,
        (Whole.induce (↑S : Set C) hClosed).IsHomomorphismEmbedding
          Target f ∧
        SetAmbientACopyIntersections A Whole Target
          (↑S : Set C) f ∧
        SetRespectsProjectedHistory p
          (↑S : Set C) f history := by
  obtain ⟨Z, Target, hTree, f, hPartial, hCopies, hHist⟩ :=
    (hSrc.weakTree_of_closed_unary_mixed_succ_closedPrev
      hUnary hA D alpha p hp hRootAlpha Base
      eAB hBase m hPrev S hS hClosed hMixedL hMixedR
      history).closed_test hClosed
  exact ⟨Z, Target, hTree, f,
    hPartial.toEHN.toFull_of_unary hUnary, hCopies, hHist⟩

end StructuralRamsey.Structure.IsFreeAmalgam

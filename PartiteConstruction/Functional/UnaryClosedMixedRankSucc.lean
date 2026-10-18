import PartiteConstruction.Structure.HomImageClosed
import PartiteConstruction.Functional.UnaryEHNCompletion
import PartiteConstruction.Functional.ClosedOccupiedAMixedRankSucc

/-!
# Unary native functional mixed tests: unconditional closed-source rank step

For unary (possibly set-valued) partial-function languages, every
EHN projection is already a FULL function homomorphism on EVERY
input (verified UnaryEHNCompletion). A full homomorphism sends
function-closed sets to closed image sets (HomImageClosed).

For a GENUINELY CLOSED exact finite weak test S of one genuine FULL
functional free attachment, each source side preimage is CLOSED.
Its part projection into the old control D is FULL (unary EHN),
so the exact projected side image is CLOSED in D.
Pulling this closed image back along selected full alpha:A↪D
makes both occupied A-boundaries CLOSED AUTOMATICALLY.

Thus the verified closed-occupied mixed rank-(m+1) theorem applies
with NO explicit occupied-boundary hypotheses. The result is a
strict full-functional Base-tree witness for the exact CLOSED
mixed test with all ambient full A-copies and projected histories.
The closed-test original-partial HE upgrades further to a FULL
homomorphism-embedding in unary languages.

This is not a general weak-test rank increment or an unconditional
all-arity n-pass sparsening theorem: nonclosed source tests may
still omit unary values and have nonclosed projected A-boundaries.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- Every genuinely function-closed finite MIXED test of size at
most m+1 in a full unary functional free attachment inherits a
STRICT full-functional Base-tree weak witness from the ordinary
rank-m predecessor over D.

There is NO occupied A-boundary closedness hypothesis: unary EHN
is full, so closed exact source side tests have closed control
images; pulling them back through alpha yields that condition.
All function fibres may be multivalued with transversal parts. -/
theorem weakTree_of_closed_unary_mixed_succ
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
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
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
  have hAlphaL : A.IsClosed {a : UA | alpha a ∈ (↑IL : Set P)} :=
    alpha.preimage_isClosed (↑IL : Set P) hIL
  have hAlphaR : A.IsClosed {a : UA | alpha a ∈ (↑IR : Set P)} :=
    alpha.preimage_isClosed (↑IR : Set P) hIR
  exact hSrc.weakTree_of_closedOccupied_alpha_mixed_succ
    hA D alpha p hp hRootAlpha Base eAB hBase m
    hPrev S hS hMixedL hMixedR hAlphaL hAlphaR history

/-- The strict unary completion of a CLOSED mixed test actually has
a FULL unary homomorphism-embedding (not merely the original-2019
source-defined partial variant) into a genuine strict full-functional
Base-tree, while retaining all ambient A-copy/history constraints.

This follows from the previously verified closed-test bridge and
unary EHN-to-full semantic equivalence. -/
theorem fullTree_of_closed_unary_mixed_succ
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
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
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
    (hSrc.weakTree_of_closed_unary_mixed_succ
      hUnary hA D alpha p hp hRootAlpha Base
      eAB hBase m hPrev S hS hClosed hMixedL hMixedR
      history).closed_test hClosed
  exact ⟨Z, Target, hTree, f,
    hPartial.toEHN.toFull_of_unary hUnary, hCopies, hHist⟩

end StructuralRamsey.Structure.IsFreeAmalgam

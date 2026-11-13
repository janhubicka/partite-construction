import PartiteConstruction.Functional.WeakHistoryFreeControlOccupiedMixed
import PartiteConstruction.Functional.MixedProjectedSideBudgets

/-!
# Track D: exact weak functional rank successor for a genuine mixed free cut

English proof committed BEFORE this Lean code:
docs/track-d-english-historyfree-exact-weak-mixed-rank-20261112.md

Weaken the overstrong arbitrary-projected-history invariant to ordinary
strict functional tree completion with ambient-relative weak EHN semantics
and protection of all REAL ambient full A-copy intersections.

The truly MIXED case of a FULL native functional free attachment
then follows from the ORDINARY rank-m control predecessor, using
only exact finite projected side IMAGE budgets and the actual source
part map. Source weak tests and control images need NOT be closed.
The common source separator map may be NONINJECTIVE. No targets are
required to reflect source-undefined function domains.

This is NOT the full ordered Hales–Jewett trace/n-pass theorem;
the two PURE cases and the trace/iterated interfaces must be checked.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}} {UA VB W P : Type v}

/-- Weakest natural FULL-functional strict Base-tree local invariant
needed for the ordinary-copy/power Picture trace: for EVERY EXACT
finite weak source test S of at most n vertices, find a strict B-tree,
an ambient-relative weak HE and FULL protected images of every actual
ambient A-copy. Arbitrary projected history lists are NOT required.

This does NOT assert a global injective part projection or a protected
target A-mark on unoccupied labels. -/
def AtMostNoHistory
    (A : Structure L UA) (Base : Structure L VB)
    (C : Structure L W) (part : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    SetAmbientRelativeWeakTreeWitness
      A Base C part (↑S : Set W) []

/-- Forgetting a genuine *arbitrary-history* rank-n certificate produces
the weaker, history-free strict functional rank-n invariant on the
identical exact weak tested sets. Not conversely. -/
theorem AtMostNoHistory.of_AtMost
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {part : W → P} {n : ℕ}
    (h : AtMost A Base C part n) :
    AtMostNoHistory A Base C part n := by
  intro S hS
  exact h S hS []

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}} {UA VB H E F C P : Type v}

/-- The ACTUAL full-functional source mixed weak-test rank successor
for the NO-HISTORY invariant. The old control D is required to have
ordinary strict functional weak tree witnesses on exact ≤m-vertex
subsets, including true ambient full A-copy protection, but neither
protected target A-marks nor arbitrary history diaries.

Both sides of a genuinely mixed finite exact WEAK test have fewer than
m+1 source vertices, so their exact projected control images have at
most m vertices. Those two ordinary control predecessor witnesses
supply the full occupied target A-marks needed by the checked
noninjective-root weak gluing construction.

The result retains a strict full-functional Base-tree target, exact
ambient-relative weak HE on S, and actual ambient A-copy protection.
It DOES NOT preserve any prescribed projected-history bit.
-/
theorem noHistory_weakRankSucc_mixed
    {A : Structure L UA} (hA : A.Irreducible)
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
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMostNoHistory
      A Base D (id : P → P) m)
    (S : Finset C) (hS : S.card ≤ m + 1)
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) [] := by
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
  have hControlL : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P)
      (pL '' (iL ⁻¹' (↑S : Set C))) [] := by
    rw [← hImgL]
    exact hPrev IL hCardL
  have hControlR : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P)
      (pR '' (iR ⁻¹' (↑S : Set C))) [] := by
    rw [← hImgR]
    exact hPrev IR hCardR
  have hpL : Left.IsEHNHomomorphismEmbedding D pL :=
    hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : Right.IsEHNHomomorphismEmbedding D pR :=
    hp.comp iR.isEHNHomomorphismEmbedding
  exact hSrc.ambientRelativeWeakTree_noHistory_of_ordinaryControlSideImages
    hA (↑S : Set C) D alpha p pL pR
    (fun _ => rfl) (fun _ => rfl)
    hpL hpR hRootAlpha Base hControlL hControlR

end StructuralRamsey.Structure.IsFreeAmalgam

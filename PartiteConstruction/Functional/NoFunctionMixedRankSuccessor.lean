import PartiteConstruction.Functional.SharpMixedRankFrontier

/-!
# Track D: unconditional mixed rank increment for function-free languages

The native functional partial-map/weak-test induction is already
machine-checked except for the maximal-rank branch with NONCLOSED
occupied A-boundaries (SharpMixedRankFrontier). When the signature
has no function symbols, every vertex subset is automatically closed.

This file removes precisely that obstruction and proves the genuine
mixed exact-weak-test successor rank theorem for arbitrary relational
signatures, using the SAME native Structure/IsFreeAmalgam/EHN API
as in the functional Appendix A. There is no relational-U-closed
replacement, no additional generated-closure budget, and no strict
target extension schema assumed.

The theorem is conditional only on the true rank-m predecessor
history witness in D and the actual full-functional free attachment
with an original-2019/EHN part projection. Thus the three-line C7
fixture with K3 control does NOT contradict it: that control fails the
rank-m predecessor hypothesis for m >= 3.

This is a sharp positive sanity check on the functional obstruction:
the genuinely open case cannot be solved merely by ordinary source
free-amalgamation geometry; it must address nonclosed occupied
boundaries of positive-arity operations and compatible target roots.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {X : Type v}

/-- For a signature without function symbols every exact vertex
subset is closed, including empty sets, and there is no reason to
replace weak tests by a generated hull. -/
theorem allSubsetsClosed_of_noFunctionSymbols
    [IsEmpty L.FuncSymbol]
    (A : Structure L X) (S : Set X) :
    A.IsClosed S := by
  intro F
  exact isEmptyElim F

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- The genuine native, exact-vertex strict full-functional mixed
rank increment is UNCONDITIONAL in a language with no function
symbols: the only remaining maximal-image obstruction from the
verified general reduction is the existence of a nonclosed occupied
alpha(A)-boundary, which is impossible in this signature.

This conclusion includes the exact n=m+1 vertex bound, actual
ambient A-copy intersections and arbitrary finite projected
histories, not just an unmarked one-copy completion. -/
theorem weakTree_mixed_succ_of_noFunctionSymbols
    [IsEmpty L.FuncSymbol]
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
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) history := by
  rcases hSrc.weakTree_or_maximal_nonclosed_alpha_mixed_succ
      hA D alpha p hp hRootAlpha Base eAB hBase
      m hPrev S hS hMixedL hMixedR history with
      hGood | ⟨_hMax, hBad⟩
  · exact hGood
  · rcases hBad with hBadLeft | hBadRight
    · exact False.elim
        (hBadLeft (Structure.allSubsetsClosed_of_noFunctionSymbols A _))
    · exact False.elim
        (hBadRight (Structure.allSubsetsClosed_of_noFunctionSymbols A _))

end StructuralRamsey.Structure.IsFreeAmalgam

import PartiteConstruction.Functional.ClosedOccupiedAMixedRankSucc
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Sharp native strict functional mixed-rank reduction

One ACTUAL FULL function-language free attachment, with exact
weak tested vertices, original-partial EHN projection, and strict
full-functional rank-m predecessor history witnesses, satisfies:

* either the exact weak mixed test of size ≤m+1 has a genuine strict
  full-functional Base-tree completion with all A-intersections
  and arbitrary projected histories;
* or the projection is MAXIMAL of size m+1 and at least one of its
  occupied alpha(A) side boundaries is NOT function-closed in A.

The small-image case pulls back the exact rank-m witness through EHN.
In the maximal-image case, BOTH closed occupied side boundaries
give the checked genuine successor-rank theorem.

No generated closure changes the test cardinality, no source-undefined
domains are reflected through p, no global fixed A-mark is asserted,
and no arbitrary-stage nonclosed mixed TARGET root completion is
fabricated. The last disjunct remains the exact genuine HJ/history
existence frontier of the strict functional Appendix A iteration.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- In the actual native function-language free-attachment induction,
EVERY finite mixed exact weak test S of |S|≤m+1 either has the desired
strict full-functional Base-tree history witness, or its projection
to the original functional control D is maximal and at least one
occupied selected alpha(A)-boundary is not function-closed.

The latter is a genuine open mathematical case: do NOT turn this
disjunction into an unconditional rank increment without a proof
of history-compatible strict TARGET B-tree root completion. -/
theorem weakTree_or_maximal_nonclosed_alpha_mixed_succ
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
      A Base Whole p (↑S : Set C) history ∨
      ((S.image p).card = m + 1 ∧
        (¬ A.IsClosed {a : UA |
          alpha a ∈ ((↑(Finset.image (p ∘ iL)
            ((Finset.univ : Finset E).filter (fun e => iL e ∈ S)))) : Set P)}
        ∨
        ¬ A.IsClosed {a : UA |
          alpha a ∈ ((↑(Finset.image (p ∘ iR)
            ((Finset.univ : Finset F).filter (fun f => iR f ∈ S)))) : Set P)})) := by
  classical
  have hImageBound : (S.image p).card ≤ m + 1 :=
    (Finset.card_image_le).trans hS
  by_cases hSmall : (S.image p).card ≤ m
  · left
    have hImageSet :
        (↑(S.image p) : Set P) = p '' (↑S : Set C) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
        exact ⟨x, hx, hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hD : SetAmbientRelativeWeakTreeWitness
        A Base D (id : P → P) (p '' (↑S : Set C)) history := by
      rw [← hImageSet]
      exact hPrev (S.image p) hSmall history
    exact (SetAmbientRelativeWeakTreeWitness.pullback_ehn
      hp hA (↑S : Set C) history hD)
  · have hMax : (S.image p).card = m + 1 := by
      omega
    by_cases hClosedL : A.IsClosed {a : UA |
        alpha a ∈ ((↑(Finset.image (p ∘ iL)
          ((Finset.univ : Finset E).filter (fun e => iL e ∈ S)))) : Set P)}
    · by_cases hClosedR : A.IsClosed {a : UA |
          alpha a ∈ ((↑(Finset.image (p ∘ iR)
            ((Finset.univ : Finset F).filter (fun f => iR f ∈ S)))) : Set P)}
      · left
        exact hSrc.weakTree_of_closedOccupied_alpha_mixed_succ
          hA D alpha p hp hRootAlpha Base eAB hBase
          m hPrev S hS hMixedL hMixedR hClosedL hClosedR history
      · right
        exact ⟨hMax, Or.inr hClosedR⟩
    · right
      exact ⟨hMax, Or.inl hClosedL⟩

end StructuralRamsey.Structure.IsFreeAmalgam

import PartiteConstruction.Functional.InjectiveRelativePullback
import PartiteConstruction.Functional.QuotientProjectedHistoryGlue

/-! # Mixed functional gluing under an injective full projection

In the maximal projected-image branch of one Picture step, cardinal equality
forces the part projection to be injective on the tested closed structure.
If function-domain reflection also holds there, the EHN projection upgrades
to a full homomorphism-embedding.

This file packages the resulting mixed step.  Each side is pulled back from
the lower-level projected-history oracle with the same prescribed A-labels on
the overlap.  The relative witnesses provide exact root isolation, so the
full functional lift glues them into a genuine strict Base-tree.

Thus, after this lemma, the genuinely new functional obstruction in the hard
branch is only failure of function-domain reflection.
-/

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {U P VB H E F C : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}

/-- A mixed source free amalgam has a strict functional Base-tree completion
when its projection to D is both full and injective and the common source root
has one prescribed A-labelling in D.

The two side generator bounds are the only local-size input. -/
theorem glueProjectedFull_injectiveProjection
    [Fintype E] [Fintype F]
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (p : C → P)
    (hp : Whole.IsHomomorphismEmbedding D p)
    (hinj : Function.Injective p)
    (beta : Embedding A D)
    (q : H → U)
    (hprojL : ∀ d, p (iL (sL d)) = beta (q d))
    (hprojR : ∀ d, p (iR (sR d)) = beta (q d))
    (m : ℕ)
    (hD :
      FunctionalProjectedHistoryTreeLike
        (A := A) (D := D) (C := D) (Base := Base) id m)
    (hgenL : Left.GeneratedByAtMost m)
    (hgenR : Right.GeneratedByAtMost m) :
    HasTreeCompletion Base Whole := by
  classical
  let pL : E → P := p ∘ iL
  let pR : F → P := p ∘ iR
  have hpL : Left.IsHomomorphismEmbedding D pL :=
    hp.comp iL.isHomomorphismEmbedding
  have hpR : Right.IsHomomorphismEmbedding D pR :=
    hp.comp iR.isHomomorphismEmbedding
  have hinjL : Function.Injective pL := by
    intro x y hxy
    apply iL.injective
    apply hinj
    exact hxy
  have hinjR : Function.Injective pR := by
    intro x y hxy
    apply iR.injective
    apply hinj
    exact hxy
  have hrootL : ∀ d, pL (sL d) = beta (q d) := by
    intro d
    exact hprojL d
  have hrootR : ∀ d, pR (sR d) = beta (q d) := by
    intro d
    exact hprojR d

  obtain ⟨ZL, TL, hTreeL, fL, hfL, _hHistL,
      targetL, hcompatL, hisoL⟩ :=
    hD.relativeWitness_of_injective_projection
      hA eAB hpL hinjL hgenL [] sL beta q hrootL
  obtain ⟨ZR, TR, hTreeR, fR, hfR, _hHistR,
      targetR, hcompatR, hisoR⟩ :=
    hD.relativeWitness_of_injective_projection
      hA eAB hpR hinjR hgenR [] sR beta q hrootR

  have hcL : targetL.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetL, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcR : targetR.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetR, ?_⟩
    intro a
    exact ⟨a, rfl⟩

  obtain ⟨Z, Target, hTree, f, hf, _hHist⟩ :=
    glueIsolatedRoot_withProjectedHistory
      (Base := Base)
      hSrc hTreeL hTreeR hcL hcR
      q fL fR hcompatL hcompatR hfL hfR hisoL hisoR
      p pL pR beta
      (fun x => rfl) (fun x => rfl)
      hrootL hrootR
      [] (by intro K hK; simp at hK) (by intro K hK; simp at hK)
  exact ⟨Z, Target, hTree, f, hf⟩

end StructuralRamsey.Structure.LocallyClosedTreeCompletable

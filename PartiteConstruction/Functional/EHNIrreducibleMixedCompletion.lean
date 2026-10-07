import PartiteConstruction.Functional.FiniteHistoryInduction
import PartiteConstruction.Functional.EHNClosedPullbackRootDichotomy

/-! # Close the irreducible-root case of functional mixed history completion

A mixed closed functional attachment splits over its actual closed common
separator.  If that separator is irreducible, the EHN projection represents
its labels by a full embedding into A.  Relative histories on the two sides
can then be rooted at the same Base-copy, with a common projection on that
copy.  Their strict extensions glue to a history-preserving completion.

No injectivity of the global outer projection is required.  This lemma
isolates the genuinely remaining case: a reducible common separator.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {U P VB H E F C : Type v}
variable {A : Structure L U} {Douter : Structure L P}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- The irreducible common separator in a full functional attachment has
compatible strict relative histories: the EHN root map is realized in A,
both side completions use one Base-root, and their free gluing preserves
all requested projected histories.  The required side invariants are the
actual generator-rank histories, not whole-stage size bounds. -/
theorem projectedHistoryCompletion_of_irreducibleEHN_root
    [Fintype E] [Fintype F] [Finite VB] [Nonempty P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (eAB : Embedding A Base) (beta : Embedding A Douter)
    (n : ℕ) (p : C → P)
    (hSideLeft : FunctionalHistoryTreeLike
      (A := A) (D := Douter) (C := Left) (Base := Base)
      (p ∘ iL) n)
    (hSideRight : FunctionalHistoryTreeLike
      (A := A) (D := Douter) (C := Right) (Base := Base)
      (p ∘ iR) n)
    (hGenLeft : Left.GeneratedByAtMost n)
    (hGenRight : Right.GeneratedByAtMost n)
    (q : H → U)
    (hEHN : Root.IsEHNHomomorphismEmbedding A q)
    (hRoot : Root.Irreducible)
    (hProjLeft : ∀ d, p (iL (sL d)) = beta (q d))
    (hProjRight : ∀ d, p (iR (sR d)) = beta (q d)) :
    HasProjectedHistoryTreeCompletion Base Whole p := by
  classical
  obtain ⟨ell, hEll⟩ :=
    hEHN.2 Root hRoot (Embedding.id Root)
  have hLabel (d : H) : ell d = q d := by
    simpa using hEll d
  obtain ⟨pBase, hBaseProj⟩ :=
    projectedMap_factors_of_kernel
      (fun a : U => beta a) (fun a : U => eAB a)
      (by
        intro a b hab
        exact congrArg (fun a : U => beta a) (eAB.injective hab))
  have hLeftLabel : ∀ d, (p ∘ iL) (sL d) = beta (ell d) := by
    intro d
    calc
      (p ∘ iL) (sL d) = beta (q d) := hProjLeft d
      _ = beta (ell d) := congrArg beta (hLabel d).symm
  have hRightLabel : ∀ d, (p ∘ iR) (sR d) = beta (ell d) := by
    intro d
    calc
      (p ∘ iR) (sR d) = beta (q d) := hProjRight d
      _ = beta (ell d) := congrArg beta (hLabel d).symm
  have hRelLeft : FunctionalRelativeHistoryTreeLike
      (A := A) (D := Douter) (C := Left) (Base := Base)
      (p ∘ iL) n :=
    FunctionalRelativeHistoryTreeLike.ofHistory hA eAB hSideLeft
  have hRelRight : FunctionalRelativeHistoryTreeLike
      (A := A) (D := Douter) (C := Right) (Base := Base)
      (p ∘ iR) n :=
    FunctionalRelativeHistoryTreeLike.ofHistory hA eAB hSideRight
  intro history
  have hShared : HasCommonRootedProjectedHistoryCompletions
      (Base := Base) sL sR (p ∘ iL) (p ∘ iR) history :=
    FunctionalRelativeHistoryTreeLike.commonRootedProjectedHistory_embeddedLabels
      hA hBase eAB hRelLeft hRelRight
      hGenLeft hGenRight ell beta
      hLeftLabel hRightLabel pBase
      (fun a => (hBaseProj a).symm) history
  obtain ⟨Z, Target, hTree, f, hf, hHistory⟩ :=
    HasCommonRootedProjectedHistoryCompletions.glue
      hSrc p (p ∘ iL) (p ∘ iR)
      (fun _ => rfl) (fun _ => rfl) history hShared
  exact ⟨Z, Target, hTree, f, hf, hHistory⟩

end StructuralRamsey.Structure.IsFreeAmalgam

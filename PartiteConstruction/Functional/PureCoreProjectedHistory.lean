import PartiteConstruction.Functional.PureCoreDomainReflection
import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion

/-! # Projected histories in a functional Hales--Jewett core

Once function-domain reflection is known on a closed core test, the weak EHN
projection becomes a full homomorphism-embedding there.  The rest of the
projected-history witness is then completely rigid: map the test by its
A-part into one fixed copy of Base.

This isolates the genuinely functional obstruction in the pure-core branch.
All tree geometry, partial-A intersection control, and arbitrary finite
projected histories are automatic; only domain reflection remains to be
proved (or descended to an earlier stage).
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P V W : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {Base : Structure L V}
variable {E : System L U W}

/-- A closed test in a weakly A-partite functional core has a one-copy
projected-history witness as soon as function-domain nonemptiness reflects on
that test.

The outer projection is alpha composed with E.part, as in the relabelled
Hales--Jewett core used by one EHN Picture step. -/
theorem pureCore_projectedHistory_of_domainReflection
    (hA : A.Irreducible)
    (hE : E.WeaklyPartiteOver A)
    (eAB : Embedding A Base)
    (alpha : Embedding A D)
    (S : Finset W)
    (hS : E.toStructure.IsClosed (↑S : Set W))
    (hreflect :
      ∀ F (x : Fin (L.funcArity F) → ↥(↑S : Set W)),
        (A.func F
          ((E.part ∘ Subtype.val) ∘ x)).Nonempty →
        ((E.toStructure.induce (↑S : Set W) hS).func F x).Nonempty)
    (history : List (Set P)) :
    let p : W → P := alpha ∘ E.part
    ∃ f : ↥(↑S : Set W) → V,
      (E.toStructure.induce (↑S : Set W) hS)
        .IsHomomorphismEmbedding Base f ∧
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := E.toStructure) (T := Base)
        p S f ∧
      FunctionalRespectsProjectedHistory p S f history := by
  classical
  let Small := E.toStructure.induce (↑S : Set W) hS
  let q : ↥(↑S : Set W) → U := E.part ∘ Subtype.val
  let p : W → P := alpha ∘ E.part
  have hq :
      Small.IsHomomorphismEmbedding A q :=
    IsEHNHomomorphismEmbedding.restrictClosed_toFull_of_domainReflection
      hE (↑S : Set W) hS hreflect
  let f : ↥(↑S : Set W) → V := eAB ∘ q
  have hf : Small.IsHomomorphismEmbedding Base f :=
    eAB.isHomomorphismEmbedding.comp hq

  have hPart :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := E.toStructure) (T := Base)
        p S f := by
    intro beta H hH e hproj hRange
    let betaH : Embedding (A.induce H hH) D :=
      beta.comp (inclusion A H hH)
    have hbetaRange :
        ∀ x : ↥H, ∃ a : U, betaH x = alpha a := by
      intro x
      refine ⟨E.part (e x), ?_⟩
      calc
        betaH x = beta x.1 := rfl
        _ = p (e x) := (hproj x).symm
        _ = alpha (E.part (e x)) := rfl
    let ell : Embedding (A.induce H hH) A :=
      betaH.factorThroughClosedRange alpha hbetaRange
    have hell (x : ↥H) :
        alpha (ell x) = beta x.1 := by
      calc
        alpha (ell x) = betaH x :=
          Embedding.factorThroughClosedRange_spec
            betaH alpha hbetaRange x
        _ = beta x.1 := rfl
    let eHT : Embedding (A.induce H hH) Base :=
      eAB.comp ell
    have heHT :
        ∀ x, eHT x = f ⟨e x, hRange x⟩ := by
      intro x
      apply eAB.injective
      apply alpha.injective
      calc
        alpha (ell x) = beta x.1 := hell x
        _ = p (e x) := (hproj x).symm
        _ = alpha (E.part (e x)) := rfl
        _ = alpha (q ⟨e x, hRange x⟩) := rfl
    have hcHT : eHT.ContainedInIrreducible := by
      refine ⟨U, A, hA, eAB, ?_⟩
      intro x
      exact ⟨ell x, rfl⟩
    exact ⟨eHT, heHT, hcHT⟩

  have hKernel :
      ∀ x y : ↥(↑S : Set W), f x = f y →
        p x.1 = p y.1 := by
    intro x y hxy
    have hqxy : q x = q y := by
      apply eAB.injective
      exact hxy
    change alpha (E.part x.1) = alpha (E.part y.1)
    exact congrArg alpha hqxy

  have hHist :
      FunctionalRespectsProjectedHistory p S f history :=
    FunctionalProjectedHistoryTreeLike.respectsHistory_of_kernel_refines_projection
      (p := p) hKernel history

  exact ⟨f, hf, hPart, hHist⟩

/-- The same witness, packaged with its one-copy strict Base-tree. -/
theorem pureCore_projectedHistoryTree_of_domainReflection
    (hA : A.Irreducible)
    (hE : E.WeaklyPartiteOver A)
    (eAB : Embedding A Base)
    (alpha : Embedding A D)
    (S : Finset W)
    (hS : E.toStructure.IsClosed (↑S : Set W))
    (hreflect :
      ∀ F (x : Fin (L.funcArity F) → ↥(↑S : Set W)),
        (A.func F
          ((E.part ∘ Subtype.val) ∘ x)).Nonempty →
        ((E.toStructure.induce (↑S : Set W) hS).func F x).Nonempty)
    (history : List (Set P)) :
    let p : W → P := alpha ∘ E.part
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (E.toStructure.induce (↑S : Set W) hS)
          .IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := E.toStructure) (T := Target)
          p S f ∧
        FunctionalRespectsProjectedHistory p S f history := by
  let p : W → P := alpha ∘ E.part
  obtain ⟨f, hf, hPart, hHist⟩ :=
    pureCore_projectedHistory_of_domainReflection
      hA hE eAB alpha S hS hreflect history
  have hTree : TreeAmalgam Base V Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro b
      exact ⟨b, rfl⟩)
  exact ⟨V, Base, hTree, f, hf, hPart, hHist⟩

end StructuralRamsey.FunctionalPartite

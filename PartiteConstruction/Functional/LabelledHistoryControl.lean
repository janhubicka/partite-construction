import PartiteConstruction.Functional.LabelledIntersectionControl
import PartiteConstruction.Functional.HistoryTreeCompletion

/-! # Functional history witnesses with labelled quotient roots

The existing synchronized history witness can be completed so that every
ambient A-copy is controlled by a whole target A-copy. Choosing the target
labels pointwise gives functional labelled-intersection controls; because the
tested set is closed, each resulting label image is a genuine closed quotient
root.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U V P W : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {C : Structure L W}
variable {Base : Structure L V}
variable {p : W → P}
variable {n : ℕ}

namespace FunctionalHistoryTreeLike

/-- Synchronized history witness together with labelled quotient-root control
for every ambient A-copy. -/
theorem witness_withLabelledControls
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory p S f projectedHistory ∧
        FunctionalRespectsSourceHistory S f sourceHistory ∧
        ∀ α : Embedding A C,
          Nonempty
            (FunctionalLabelledIntersectionControl
              (A := A) (C := C) (T := Target) S f α) := by
  obtain ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc, hctrl⟩ :=
    h.witness_withControl hA eAB hp S hS hgen
      projectedHistory sourceHistory
  refine ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc, ?_⟩
  exact FunctionalLabelledIntersectionControl.of_controls hctrl

end FunctionalHistoryTreeLike

end StructuralRamsey.Structure

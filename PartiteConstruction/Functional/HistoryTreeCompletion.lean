import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion
import PartiteConstruction.Functional.ControlCompletion

/-! # Combined projected/source histories for functional local tree completion

The relational sparsening proof only needs histories of subsets of the ambient
part structure D.  For set-valued functions this is not sufficient when two
source vertices occupy the same part: fibre-surjectivity in a mixed free
amalgam also needs to know that points outside the actual source overlap are
not identified with points inside it.

Accordingly the functional diary carries two finite histories:
* projected subsets of D, for the existing partite bookkeeping;
* actual subsets of the current source C, for root isolation.

The final local tree-completion statement forgets both histories.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}

/-- Functional projected-history invariant strengthened by arbitrary finite
source-side history. -/
def FunctionalHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ (projectedHistory : List (Set P))
      (sourceHistory : List (Set W)),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory

namespace FunctionalHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Forget source history. -/
theorem toProjectedHistory
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  intro S hS hgen history
  obtain ⟨Z, T, hTree, f, hf, hPart, hProj, _⟩ :=
    h S hS hgen history []
  exact ⟨Z, T, hTree, f, hf, hPart, hProj⟩

/-- Forget all diary data. -/
theorem toLocallyClosedTreeCompletable
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyClosedTreeCompletable Base C n :=
  h.toProjectedHistory.toLocallyClosedTreeCompletable

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hgen hp hs
  exact h S hS (hgen.mono hmn) hp hs

/-- If the witness map is injective then it respects every source history. -/
theorem respectsSourceHistory_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (history : List (Set W)) :
    FunctionalRespectsSourceHistory S f history := by
  intro H _ x y hxy
  have hxy' : x = y := hf hxy
  subst y
  rfl

/-- If equality in the target already implies equality of source vertices,
both kinds of finite history are automatic. -/
theorem histories_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    FunctionalRespectsProjectedHistory p S f projectedHistory ∧
      FunctionalRespectsSourceHistory S f sourceHistory := by
  constructor
  · intro H _ x y hxy
    have hxy' : x = y := hf hxy
    subst y
    rfl
  · exact respectsSourceHistory_of_injective hf sourceHistory

end FunctionalHistoryTreeLike

end StructuralRamsey.Structure

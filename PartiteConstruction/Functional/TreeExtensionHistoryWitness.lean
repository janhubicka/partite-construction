import PartiteConstruction.Functional.TreeExtensionHistoryGlue
import PartiteConstruction.Functional.TreeExtensionWitness

/-! # Relative strict root-tree witnesses retaining projected histories

The functional reducible-root induction needs a stronger predicate than bare
existence of a tree completion: each side must extend the *same* completed
overlap, be isolated from the distinguished root tree away from its own
source root, and retain a chosen finite projected diary.

The predicates below package exactly these hypotheses.  Their gluing
theorem uses strict replay/merge, not an unjustified embedding of a
reducible overlap into one irreducible Base-copy.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {VB H E F C P G : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Side : Structure L E}
variable {Start : Structure L G}

/-- A full side completion relative to one prescribed strict root tree,
retaining a finite list of subsets of the outer projection. -/
def HasTreeExtensionProjectedHistoryCompletion
    (s : Embedding Root Side) (q : H → G)
    (p : E → P) (history : List (Set P)) : Prop :=
  ∃ (Z : Type v) (Target : Structure L Z)
    (hExt : TreeExtension Base Start Z Target)
    (f : E → Z),
      Side.IsHomomorphismEmbedding Target f ∧
      (∀ d, f (s d) = hExt.startEmbedding (q d)) ∧
      IsFreeAmalgam.RootIsolated s hExt.startEmbedding q f ∧
      (∀ K ∈ history, ∀ x y : E,
        f x = f y → (p x ∈ K ↔ p y ∈ K))

namespace HasTreeExtensionProjectedHistoryCompletion

/-- Forgetting finite projected histories recovers the strict relative
completion already used by the irreducible-root argument. -/
theorem toTreeExtension
    {s : Embedding Root Side} {q : H → G}
    {p : E → P} {history : List (Set P)}
    (h : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p history) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start) s q := by
  obtain ⟨Z, Target, hExt, f, hf, hcompat, hroot, _⟩ := h
  exact ⟨Z, Target, hExt, f, hf, hcompat, hroot⟩

end HasTreeExtensionProjectedHistoryCompletion

/-- The two side completions share the same strict target root tree and
the same projected values on its source root.  The root label map may be
noninjective. -/
def HasCommonRootedProjectedHistoryCompletions
    {Right : Structure L F}
    (sL : Embedding Root Side) (sR : Embedding Root Right)
    (pL : E → P) (pR : F → P)
    (history : List (Set P)) : Prop :=
  ∃ (G₀ : Type v) (Start₀ : Structure L G₀),
    TreeAmalgam Base G₀ Start₀ ∧
    ∃ q : H → G₀,
      Root.IsHomomorphismEmbedding Start₀ q ∧
      ∃ pG : G₀ → P,
        (∀ d, pL (sL d) = pG (q d)) ∧
        (∀ d, pR (sR d) = pG (q d)) ∧
        HasTreeExtensionProjectedHistoryCompletion
          (Base := Base) (Start := Start₀) sL q pL history ∧
        HasTreeExtensionProjectedHistoryCompletion
          (Base := Base) (Start := Start₀) sR q pR history

namespace HasCommonRootedProjectedHistoryCompletions

/-- Functional mixed gluing over a possibly reducible completed root,
preserving the finite projected history. -/
theorem glue
    {Whole : Structure L C} {Right : Structure L F}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    {iL : Embedding Side Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpL : ∀ x, pWhole (iL x) = pL x)
    (hpR : ∀ x, pWhole (iR x) = pR x)
    (history : List (Set P))
    (h : HasCommonRootedProjectedHistoryCompletions
      (Base := Base) sL sR pL pR history) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C → Z,
        Whole.IsHomomorphismEmbedding Target f ∧
        (∀ K ∈ history, ∀ x y : C,
          f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K)) := by
  obtain ⟨G₀, Start₀, hStart, q, _hq, pG,
    hqL, hqR, hL, hR⟩ := h
  obtain ⟨ZL, TL, hExtL, fL, hfL, hcompatL, hrootL,
    hHistL⟩ := hL
  obtain ⟨ZR, TR, hExtR, fR, hfR, hcompatR, hrootR,
    hHistR⟩ := hR
  exact LocallyClosedTreeCompletable.glueTreeExtensions_withProjectedHistory
    hSrc hStart hExtL hExtR q
    fL fR hcompatL hcompatR hfL hfR hrootL hrootR
    pWhole pL pR pG hpL hpR hqL hqR
    history hHistL hHistR

end HasCommonRootedProjectedHistoryCompletions

end StructuralRamsey.Structure

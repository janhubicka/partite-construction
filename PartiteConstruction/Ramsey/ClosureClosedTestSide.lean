import PartiteConstruction.Ramsey.ClosureUIrreducibleEquivalence
import PartiteConstruction.Ramsey.ClosureRelativeIrreducibleWeakTest

/-! # Intrinsic U-irreducible *closed* tests in semi-closed free amalgams

The published 2019 Picture argument needs localization of U-irreducible
copies when gluing semi-closed structures. On a genuinely U-closed
tested structure, intrinsic U-irreducibility and relative
U-irreducibility agree (verified separately). The relative weak-test
side-localization theorem can therefore be applied.

No such conclusion follows for an arbitrary *nonclosed* intrinsically
U-irreducible weak test: the missing-output obstruction is a separate
checked theorem. This file records the safe local induction interface,
including an exact embedding into the appropriate side.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Intrinsic U-irreducibility localizes to one free-amalgam side for
U-closed tests, even if the whole picture and either side are merely
U-semi-closed. The tested set is unchanged. -/
theorem IsFreeAmalgam.uIrreducible_closedTest_side
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (S : Set C)
    (hClosed : IsUClosed rules (Whole.induce S))
    (hIrred : IsUIrreducible rules (Whole.induce S)) :
    (∀ z : S, ∃ a : E, z.1 = iL a) ∨
    (∀ z : S, ∃ b : F, z.1 = iR b) := by
  have hRelative :
      IsURelativelyIrreducible rules (Whole.induce S) :=
    (hClosed.uIrreducible_iff_relative).mp hIrred
  exact hFree.uRelativeIrreducible_weak_side
    hCommon hLeft hRight S hRelative

/-- Stronger exact form: an intrinsically U-irreducible U-closed test
fully embeds into one *original* side, and the embedding still
commutes with that side's given inclusion into the free amalgam. -/
theorem IsFreeAmalgam.uIrreducible_closedTest_factor
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (S : Set C)
    (hClosed : IsUClosed rules (Whole.induce S))
    (hIrred : IsUIrreducible rules (Whole.induce S)) :
    (∃ g : Embedding (Whole.induce S) Left,
      ∀ x : S, iL (g x) = x.1) ∨
    (∃ g : Embedding (Whole.induce S) Right,
      ∀ x : S, iR (g x) = x.1) := by
  classical
  let inc : Embedding (Whole.induce S) Whole :=
    inclusion Whole S
  rcases hFree.uIrreducible_closedTest_side
      hCommon hLeft hRight S hClosed hIrred with hOnLeft | hOnRight
  · left
    have hRange (x : S) : ∃ a : E, inc x = iL a :=
      hOnLeft x
    let g : Embedding (Whole.induce S) Left :=
      inc.factorThroughRange iL hRange
    refine ⟨g, ?_⟩
    intro x
    change iL (Classical.choose (hRange x)) = x.1
    exact (Classical.choose_spec (hRange x)).symm
  · right
    have hRange (x : S) : ∃ b : F, inc x = iR b :=
      hOnRight x
    let g : Embedding (Whole.induce S) Right :=
      inc.factorThroughRange iR hRange
    refine ⟨g, ?_⟩
    intro x
    change iR (Classical.choose (hRange x)) = x.1
    exact (Classical.choose_spec (hRange x)).symm

end StructuralRamsey.RelStructure

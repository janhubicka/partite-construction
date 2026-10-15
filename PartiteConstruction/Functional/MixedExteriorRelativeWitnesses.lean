import PartiteConstruction.Functional.MixedExteriorGeneratorBudget
import PartiteConstruction.Functional.OriginalPartialIrreducibleRootRelativeWitness
import PartiteConstruction.Functional.OriginalPartialSmallImageGeneratorHull

/-!
# Exterior generator reserves give compatible strict relative B-trees

The verified native functional strict local-tree iteration still needs
two compatible relative completions of a genuinely mixed closed test
over its actual common full-functional separator.

For an IRREDUCIBLE common separator, the synchronization step is now
fully verified: any two absolute strict original-2019 partial-function
side completions can be attached over the SAME prescribed B-copy.

The remaining question is the rank of those two sides. The already
verified finite generator-budget theorem replaces the crude
rank(Left) <= n + |Root| with a more precise accounting:
if the common root has a generating set R and the source has an
exterior reserve OutLeft outside the closed left side, then
rank(Left) <= n whenever |R| <= |OutLeft|.

This file combines these two independently certified lemmas. It gives
a complete pair of compatible strict relative B-tree side witnesses
whenever BOTH sides have adequate exterior generator reserves and the
root is irreducible, regardless of the root's vertex cardinality or
generator rank.

A genuine native maximal mixed test need not satisfy this reserve
condition automatically; roots requiring too many independent
generators remain the mathematical problem. No total-fibre projection
or U-closed relational Ramsey construction is used.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C VB : Type v}

/-- Given an irreducible embedded common root and exterior generator
reserves paying for its generating set on BOTH sides, construct two
compatible relative strict original-partial B-tree completions over
one fixed full copy of Base. This does not assume independently chosen
target completions are already synchronized. -/
theorem compatibleOriginalPartialRelativeCompletions_of_exterior_root_budget
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite H] [Finite E] [Finite F]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB) (hBase : Base.Irreducible)
    (hRoot : Root.Irreducible)
    (q : Embedding Root Base)
    (n : ℕ)
    (G : Finset C) (hGgen : Whole.GeneratedBy (↑G : Set C))
    (hGCard : G.card ≤ n)
    (R : Finset H) (hRgen : Root.GeneratedBy (↑R : Set H))
    (OutLeft OutRight : Finset C)
    (hOutLeftSubset : OutLeft ⊆ G)
    (hOutRightSubset : OutRight ⊆ G)
    (hOutLeft : ∀ x ∈ OutLeft, x ∉ Set.range iL)
    (hOutRight : ∀ x ∈ OutRight, x ∉ Set.range iR)
    (hLeftBudget : R.card ≤ OutLeft.card)
    (hRightBudget : R.card ≤ OutRight.card)
    (hLeftRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Left n)
    (hRightRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Right n) :
    HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sL q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sR q := by
  classical
  have hLeftGen : Left.GeneratedByAtMost n :=
    hFree.left_generatedByAtMost_of_exterior_root_seeds
      G hGgen R hRgen OutLeft hOutLeftSubset
      hOutLeft hLeftBudget hGCard
  have hRightGen : Right.GeneratedByAtMost n :=
    hFree.swap.left_generatedByAtMost_of_exterior_root_seeds
      G hGgen R hRgen OutRight hOutRightSubset
      hOutRight hRightBudget hGCard
  have hLeftTree : HasOriginalPartialTreeCompletion Base Left :=
    hLeftRank.completion_of_embedding
      Left hLeftGen (Embedding.id Left)
  have hRightTree : HasOriginalPartialTreeCompletion Base Right :=
    hRightRank.completion_of_embedding
      Right hRightGen (Embedding.id Right)
  exact ⟨
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sL q hLeftTree,
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sR q hRightTree⟩

end StructuralRamsey.Structure.IsFreeAmalgam

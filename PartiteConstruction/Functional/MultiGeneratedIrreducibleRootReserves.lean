import PartiteConstruction.Functional.MixedExteriorGeneratorBudget
import PartiteConstruction.Functional.OneGeneratedRootRelativeCompletion

/-!
# Track D: multi-generated irreducible separators with paid exterior reserves

An actual full functional mixed root may need >=2 generators.
Irreducibility of the root plus a common FULL embedding into Base
synchronizes the two side completions, provided their generator
rank stays within n. The full native free-amalgam exterior budget
pays for ROOT generators with distinct WHOLE exterior generators
on both sides. No closure vertex cardinality is charged.

This proves a genuine positive subcase of the otherwise open hard
relative-root extension problem. It does NOT assert that every
Hales--Jewett history supplies the stated exterior reserves.
Reducible common roots and insufficient exterior reserves remain open.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam
universe u v
variable {L : Language.{u}}
variable {H E F C VB UA : Type v}

/-- Both original-partial relative Base-tree completions use the
SAME prescribed full irreducible root map, even if that root
needs more than one generator. The requisite root seed budget
is paid separately from each side's exterior whole generators. -/
theorem compatibleOriginalPartialRelativeCompletions_irr_root_reserves
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
    (n : ℕ) (G : Finset C)
    (hWholeGen : Whole.GeneratedBy (↑G : Set C))
    (hGcard : G.card ≤ n)
    (Roots : Finset H)
    (hRootGen : Root.GeneratedBy (↑Roots : Set H))
    (OutRight : Finset C)
    (hOutRightSub : OutRight ⊆ G)
    (hOutRightExterior : ∀ z ∈ OutRight, z ∉ Set.range iL)
    (hOutRightPays : Roots.card ≤ OutRight.card)
    (OutLeft : Finset C)
    (hOutLeftSub : OutLeft ⊆ G)
    (hOutLeftExterior : ∀ z ∈ OutLeft, z ∉ Set.range iR)
    (hOutLeftPays : Roots.card ≤ OutLeft.card)
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
      G hWholeGen Roots hRootGen OutRight
      hOutRightSub hOutRightExterior hOutRightPays hGcard
  have hRightGen : Right.GeneratedByAtMost n :=
    hFree.swap.left_generatedByAtMost_of_exterior_root_seeds
      G hWholeGen Roots hRootGen OutLeft
      hOutLeftSub hOutLeftExterior hOutLeftPays hGcard
  have hLeft : HasOriginalPartialTreeCompletion Base Left :=
    hLeftRank.completion_of_embedding
      Left hLeftGen (Embedding.id Left)
  have hRight : HasOriginalPartialTreeCompletion Base Right :=
    hRightRank.completion_of_embedding
      Right hRightGen (Embedding.id Right)
  exact ⟨
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sL q hLeft,
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sR q hRight⟩

/-- If the actual source separator is irreducible and admits an
original-2019/EHN map to selected A, that map becomes a FULL
embedding, yielding the canonical common Base root automatically.
Both sides then receive compatible relative strict B-tree targets
under the independently paid exterior reserve hypotheses. -/
theorem compatibleOriginalPartialRelativeCompletions_irr_EHN_root_reserves
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite H] [Finite E] [Finite F]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (A : Structure L UA) (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hRoot : Root.Irreducible)
    (r : H → UA)
    (hRootEHN : Root.IsEHNHomomorphismEmbedding A r)
    (eAB : Embedding A Base)
    (n : ℕ) (G : Finset C)
    (hWholeGen : Whole.GeneratedBy (↑G : Set C))
    (hGcard : G.card ≤ n)
    (Roots : Finset H)
    (hRootGen : Root.GeneratedBy (↑Roots : Set H))
    (OutRight : Finset C)
    (hOutRightSub : OutRight ⊆ G)
    (hOutRightExterior : ∀ z ∈ OutRight, z ∉ Set.range iL)
    (hOutRightPays : Roots.card ≤ OutRight.card)
    (OutLeft : Finset C)
    (hOutLeftSub : OutLeft ⊆ G)
    (hOutLeftExterior : ∀ z ∈ OutLeft, z ∉ Set.range iR)
    (hOutLeftPays : Roots.card ≤ OutLeft.card)
    (hLeftRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Left n)
    (hRightRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Right n) :
    ∃ q : Embedding Root Base,
      (∀ x : H, q x = eAB (r x)) ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sL q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sR q := by
  classical
  obtain ⟨qA, hqA⟩ :=
    hRootEHN.2 Root hRoot (Embedding.id Root)
  let q : Embedding Root Base := eAB.comp qA
  refine ⟨q, ?_, ?_⟩
  · intro x
    exact congrArg eAB (hqA x)
  · exact hFree.compatibleOriginalPartialRelativeCompletions_irr_root_reserves
      Base hBase hRoot q n G hWholeGen hGcard Roots hRootGen
      OutRight hOutRightSub hOutRightExterior hOutRightPays
      OutLeft hOutLeftSub hOutLeftExterior hOutLeftPays
      hLeftRank hRightRank
end StructuralRamsey.Structure.IsFreeAmalgam

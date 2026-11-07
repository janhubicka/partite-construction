import PartiteConstruction.Functional.OriginalPartialIrreducibleRootRelativeWitness

/-!
# Track D: relative strict Base trees for reducible roots with irreducible collars

The actual common separator of a mixed Hales--Jewett functional
attachment may be reducible even though each original source side
admits a strict original-partial absolute Base-tree completion.

An irreducible FULL substructure `Collar` of a side, containing
the FULL common separator and embedding FULLY into Base, provides
the missing synchronization: the absolute side completion is FULL
on Collar by irreducibility, so the checked irreducible-root
extension theorem attaches one prescribed Base copy along Collar.
Restricting the root law to the actual separator gives a relative
completion even when the separator itself is reducible.

For two sides, collar maps may differ away from the common
separator but must agree ON the separator in Base. Their two
relative completions then use the SAME prescribed Base root.
The checked original-partial relative gluing lemma completes the
whole free source amalgam.

This is a positive conditional ROOT-FACTOR theorem, not a claim
that arbitrary historical separators are contained in such
irreducible collars, that their canonical part maps are injective,
or that arbitrary independent strict completions synchronize.
Nothing about the literal weak tested vertex count is changed.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H K E F C VB KL KR : Type v}

/-- A reducible FULL root can be anchored relatively through an
irreducible FULL source-side COLLAR containing it.

No irreducibility of Root, no function-generated root size bound,
and no global target retraction are required. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_irreducible_collar_absolute
    {Root : Structure L H}
    {Collar : Structure L K}
    {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hCollar : Collar.Irreducible)
    (rootInCollar : Embedding Root Collar)
    (collarInSide : Embedding Collar Side)
    (toBase : Embedding Collar Base)
    (hSide : HasOriginalPartialTreeCompletion Base Side) :
    HasOriginalPartialTreeExtensionCompletion (Start := Base)
      Base (collarInSide.comp rootInCollar)
        (toBase ∘ rootInCollar) := by
  obtain ⟨Y, Target, hExt, p, hp, hRoot⟩ :=
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hCollar collarInSide toBase hSide
  refine ⟨Y, Target, hExt, p, hp, ?_⟩
  intro x
  exact hRoot (rootInCollar x)

/-- Two full source-side irreducible collars need not be identical.
Their FULL Base marks need agree only on the ACTUAL possibly
REDUCIBLE common separator. Then the two absolute strict side
completions become two RELATIVE strict Base-tree completions over
the exact SAME Base and the SAME pointwise root map.

The source root remains literal; no closure is added to it. -/
theorem compatibleOriginalPartialRelativeCompletions_of_collars
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {CollarL : Structure L KL} {CollarR : Structure L KR}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hCollarL : CollarL.Irreducible)
    (hCollarR : CollarR.Irreducible)
    (rootL : Embedding Root CollarL)
    (rootR : Embedding Root CollarR)
    (jL : Embedding CollarL Left)
    (jR : Embedding CollarR Right)
    (sL : Embedding Root Left)
    (sR : Embedding Root Right)
    (hFactorL : ∀ x : H, sL x = jL (rootL x))
    (hFactorR : ∀ x : H, sR x = jR (rootR x))
    (qL : Embedding CollarL Base)
    (qR : Embedding CollarR Base)
    (hAgree : ∀ x : H, qL (rootL x) = qR (rootR x))
    (hAbsL : HasOriginalPartialTreeCompletion Base Left)
    (hAbsR : HasOriginalPartialTreeCompletion Base Right) :
    ∃ (q : H → VB),
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sL q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sR q := by
  obtain ⟨YL, TL, eL, pL, hpL, hRootL⟩ :=
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_collar_absolute
      Base hBase hCollarL rootL jL qL hAbsL
  obtain ⟨YR, TR, eR, pR, hpR, hRootR⟩ :=
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_collar_absolute
      Base hBase hCollarR rootR jR qR hAbsR
  refine ⟨qL ∘ rootL, ?_, ?_⟩
  · refine ⟨YL, TL, eL, pL, hpL, ?_⟩
    intro x
    calc
      pL (sL x) = pL (jL (rootL x)) :=
        congrArg pL (hFactorL x)
      _ = eL.startEmbedding (qL (rootL x)) := hRootL x
  · refine ⟨YR, TR, eR, pR, hpR, ?_⟩
    intro x
    calc
      pR (sR x) = pR (jR (rootR x)) :=
        congrArg pR (hFactorR x)
      _ = eR.startEmbedding (qR (rootR x)) := hRootR x
      _ = eR.startEmbedding (qL (rootL x)) :=
        congrArg eR.startEmbedding (hAgree x).symm

/-- A free amalgam over a REDUCIBLE common root is original-partially
strict Base-tree completable whenever BOTH sides admit absolute
completions and their common root factors through suitably
aligned irreducible source collars.

This does NOT assert that such collars always exist in an
arbitrary Hales--Jewett history. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_of_aligned_irreducible_collars
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {CollarL : Structure L KL} {CollarR : Structure L KR}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (hCollarL : CollarL.Irreducible)
    (hCollarR : CollarR.Irreducible)
    (rootL : Embedding Root CollarL)
    (rootR : Embedding Root CollarR)
    (jL : Embedding CollarL Left)
    (jR : Embedding CollarR Right)
    (hFactorL : ∀ x : H, sL x = jL (rootL x))
    (hFactorR : ∀ x : H, sR x = jR (rootR x))
    (qL : Embedding CollarL Base)
    (qR : Embedding CollarR Base)
    (hAgree : ∀ x : H, qL (rootL x) = qR (rootR x))
    (hAbsL : HasOriginalPartialTreeCompletion Base Left)
    (hAbsR : HasOriginalPartialTreeCompletion Base Right) :
    HasOriginalPartialTreeCompletion Base Whole := by
  obtain ⟨q, hRelL, hRelR⟩ :=
    compatibleOriginalPartialRelativeCompletions_of_collars
      Base hBase hCollarL hCollarR
      rootL rootR jL jR sL sR hFactorL hFactorR
      qL qR hAgree hAbsL hAbsR
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  exact hSrc.originalPartialTreeCompletion_glue_relative
    Base hTree q hRelL hRelR

end StructuralRamsey.Structure

import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue

/-!
# Preserve a distinguished strict B-tree root through one more attachment

The original-2019 partial-function mixed Picture construction attaches
successive old-stage copies to one Hales--Jewett core. Merely proving
an absolute strict B-tree completion of the intermediate Picture is
insufficient: the next attachment must use a coherent copy of the
original Hales--Jewett root.

Here the LEFT Picture already has a strict relative full-functional
B-tree completion over a fixed earlier Start and a distinguished
embedded root Anchor. Given its chosen target tree TLeft and completion
map pLeft, suppose the incoming RIGHT attached stage can be completed
relatively over the actual shared separator using precisely the map
pLeft∘sL into TLeft.

The old completion tree is used as Start for the new right extension.
The canonical extension embedding transports pLeft. Because the source
attachment is a genuine full free amalgam and the maps agree on the
separator, the original 2019 partial homomorphism-embedding glues.
Concatenating TreeExtensions supplies a relative completion of the
NEW picture over the SAME original Start and Anchor.

Crucially this is a relative-to-relative preservation theorem, not
merely an unrooted strict completion. No U-closed relational replay,
new Ramsey argument, source-root isolation, or total-fibre global
homomorphism is used.

The new right-side relative witness over the already completed old
target is an EXPLICIT hypothesis. Constructing it uniformly for
maximal mixed multi-generated native separators remains open.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H0 H E F Z VB G Y : Type v}

/-- Attaching a genuine full functional source along sL and sR
preserves a distinguished older root Anchor↪Left at the level of
strict ORIGINAL-PARTIAL relative B-tree completion.

The right side is required to extend the OLD completion tree
TLeft, with prescribed root map pLeft∘sL. This is the exact
one-sided inductive interface for a sequence of star attachments.
There is no assumption that the source common root is irreducible
or that any global completion map is injective. -/
theorem IsFreeAmalgam.originalPartialTreeExtension_append
    {Anchor : Structure L H0}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (Start : Structure L G)
    (anchor : Embedding Anchor Left)
    (q : H0 → G)
    (TLeft : Structure L Y)
    (hLeftExt : TreeExtension Base Start Y TLeft)
    (pLeft : E → Y)
    (hLeft : IsOriginalPartialHomomorphismEmbedding Left TLeft pLeft)
    (hAnchor : ∀ x : H0,
      pLeft (anchor x) = hLeftExt.startEmbedding (q x))
    (hRight : HasOriginalPartialTreeExtensionCompletion
      (Start := TLeft) Base sR (pLeft ∘ sL)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base (iL.comp anchor) q := by
  obtain ⟨YR, TRight, hRightExt, pRight, hpRight, hRightRoot⟩ := hRight
  let pLeftFinal : E → YR := hRightExt.startEmbedding ∘ pLeft
  have hMapLeft : Left.IsEHNHomomorphismEmbedding
      TRight pLeftFinal :=
    hRightExt.startEmbedding.isEHNHomomorphismEmbedding.comp
      hLeft.toEHN
  have hMapRight : Right.IsEHNHomomorphismEmbedding
      TRight pRight :=
    hpRight.toEHN
  have hAgree : ∀ x : H,
      pLeftFinal (sL x) = pRight (sR x) := by
    intro x
    change hRightExt.startEmbedding (pLeft (sL x)) = pRight (sR x)
    exact (hRightRoot x).symm
  obtain ⟨p, hp, hPL, _hPR⟩ :=
    hSrc.exists_EHN_projection
      pLeftFinal pRight hMapLeft hMapRight hAgree
  let hExt : TreeExtension Base Start YR TRight :=
    hLeftExt.trans hRightExt
  refine ⟨YR, TRight, hExt, p, hp.toOriginalPartial, ?_⟩
  intro x
  calc
    p ((iL.comp anchor) x) = pLeftFinal (anchor x) := hPL (anchor x)
    _ = hRightExt.startEmbedding (pLeft (anchor x)) := rfl
    _ = hRightExt.startEmbedding (hLeftExt.startEmbedding (q x)) :=
      congrArg hRightExt.startEmbedding (hAnchor x)
    _ = hExt.startEmbedding (q x) :=
      (hLeftExt.startEmbedding_trans hRightExt (q x)).symm

/-- Existential interface for iteration: if the right side has the
required relative completion for EVERY possible left relative
witness, then a left relative completion implies a relative completion
of the entire binary free attachment over the original anchored root.

This packages only the geometric induction; Ramsey coloring,
power construction and finite attachment recursion remain unchanged. -/
theorem IsFreeAmalgam.originalPartialTreeExtension_append_exists
    {Anchor : Structure L H0}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (Start : Structure L G)
    (anchor : Embedding Anchor Left)
    (q : H0 → G)
    (hOld : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base anchor q)
    (hAttach :
      ∀ (YL : Type v) (TL : Structure L YL)
        (hLext : TreeExtension Base Start YL TL)
        (pL : E → YL),
        IsOriginalPartialHomomorphismEmbedding Left TL pL →
        (∀ x : H0, pL (anchor x) = hLext.startEmbedding (q x)) →
        HasOriginalPartialTreeExtensionCompletion
          (Start := TL) Base sR (pL ∘ sL)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base (iL.comp anchor) q := by
  obtain ⟨YL, TL, hLext, pL, hpL, hAnchor⟩ := hOld
  exact hSrc.originalPartialTreeExtension_append
    Base Start anchor q TL hLext pL hpL hAnchor
    (hAttach YL TL hLext pL hpL hAnchor)

end StructuralRamsey.Structure

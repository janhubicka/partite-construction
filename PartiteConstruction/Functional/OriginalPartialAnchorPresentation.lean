import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue

/-!
# Strict original-partial completions do not depend on anchor presentation

In the full-functional 2019 Picture induction the closed intersection
of a test with the original Hales--Jewett core can be represented by
several isomorphic FULL substructures.  A predecessor's invariant may
choose an abstract exact anchor, while the new free-amalgam pullback
chooses the canonical induced intersection.

This module shows that a relative strict B-tree completion can be
reindexed to the canonical anchor whenever the two anchor images in
the source are the same and their original-core labels commute.
The proof does NOT identify unrelated partial homomorphism maps and
never generates the closure of a weak source subset.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H0 H1 E VB G X : Type v}

/-- Reparameterise the source root of an original-2019 partial
relative strict B-tree completion along an embedding and matching
root labels.  The target tree and the original-partial map do not
change. -/
theorem HasOriginalPartialTreeExtensionCompletion.reparametrize_root
    {OldAnchor : Structure L H0}
    {NewAnchor : Structure L H1}
    {Side : Structure L E}
    {Start : Structure L G}
    (Base : Structure L VB)
    (sOld : Embedding OldAnchor Side)
    (sNew : Embedding NewAnchor Side)
    (qOld : H0 → G) (qNew : H1 → G)
    (hOld : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base sOld qOld)
    (j : Embedding NewAnchor OldAnchor)
    (hSrc : ∀ x : H1, sOld (j x) = sNew x)
    (hLabel : ∀ x : H1, qOld (j x) = qNew x) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base sNew qNew := by
  obtain ⟨Y, Target, hExt, p, hp, hRoot⟩ := hOld
  refine ⟨Y, Target, hExt, p, hp, ?_⟩
  intro x
  calc
    p (sNew x) = p (sOld (j x)) := congrArg p (hSrc x).symm
    _ = hExt.startEmbedding (qOld (j x)) := hRoot (j x)
    _ = hExt.startEmbedding (qNew x) :=
      congrArg hExt.startEmbedding (hLabel x)

/-- Transport a strict original-partial anchored witness from an
EXACT old tested-core anchor to any other fully embedded presentation
of the same actual intersection.

The old anchor is required to cover EXACTLY the points of Test whose
images lie in OriginalCore.  The new anchor need only commute with the
original-core embedding.  An embedding NewAnchor -> OldAnchor then
exists canonically by range factorisation and induces the same root
labels because the core embedding is injective.

This avoids demanding that a previous proof construct a particular
subtype of the closed test: its root-relative witness is reusable for
the canonical pullback anchor of the next Picture step. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_exact_anchor_range
    {OldAnchor : Structure L H0}
    {NewAnchor : Structure L H1}
    {Test : Structure L E}
    {OriginalCore : Structure L X}
    {TargetCore : Structure L G}
    (Base : Structure L VB)
    (oldIn : Embedding OldAnchor Test)
    (newIn : Embedding NewAnchor Test)
    (oldToCore : Embedding OldAnchor OriginalCore)
    (newToCore : Embedding NewAnchor OriginalCore)
    (testIn : Embedding Test TargetCore)
    (coreIn : Embedding OriginalCore TargetCore)
    {G0 : Type v} {Start : Structure L G0}
    (q : X → G0)
    (hOldComm : ∀ x : H0,
      testIn (oldIn x) = coreIn (oldToCore x))
    (hNewComm : ∀ x : H1,
      testIn (newIn x) = coreIn (newToCore x))
    (hOldExact : ∀ z : E,
      (∃ x : H0, oldIn x = z) ↔
      (∃ y : X, testIn z = coreIn y))
    (hOld : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base oldIn (q ∘ oldToCore)) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base newIn (q ∘ newToCore) := by
  classical
  have hRange : ∀ x : H1, ∃ y : H0, newIn x = oldIn y := by
    intro x
    obtain ⟨y, hy⟩ :=
      (hOldExact (newIn x)).mpr
        ⟨newToCore x, hNewComm x⟩
    exact ⟨y, hy.symm⟩
  let j : Embedding NewAnchor OldAnchor :=
    newIn.factorThroughRange oldIn hRange
  have hSrc : ∀ x : H1, oldIn (j x) = newIn x := by
    intro x
    exact (Classical.choose_spec (hRange x)).symm
  have hCore : ∀ x : H1, oldToCore (j x) = newToCore x := by
    intro x
    apply coreIn.injective
    calc
      coreIn (oldToCore (j x)) = testIn (oldIn (j x)) :=
        (hOldComm (j x)).symm
      _ = testIn (newIn x) := congrArg testIn (hSrc x)
      _ = coreIn (newToCore x) := hNewComm x
  exact HasOriginalPartialTreeExtensionCompletion.reparametrize_root
    Base oldIn newIn (q ∘ oldToCore) (q ∘ newToCore)
    hOld j hSrc (fun x => congrArg q (hCore x))

end StructuralRamsey.Structure

import PartiteConstruction.Functional.NativeExactWholeAnchor
import PartiteConstruction.Functional.OriginalPartialAnchorPresentation

/-!
# Exact core-anchored local completions: binary functional Picture step

The published functional Hales--Jewett Picture induction keeps the
original power core inside every intermediate stage.  A closed test
of size at most n has a canonical full closed intersection with this
core, and we want a strict ORIGINAL-2019 partial-function B-tree
completion relative to the selected A-support labels on that anchor.

This module isolates the exact local property and proves its binary
preservation under ONE explicit copied-old-side relative extension
hypothesis.  The predecessor's root witness may use a different
full presentation of the very same exact intersection: the new
anchor-presentation transfer theorem makes it canonical.

The proof is not a relational function-graph or U-closed replay.
All sides and roots are genuinely function closed, and the test
cardinality is not enlarged.  Existence of the copied-side
relative witness for hard mixed multi-generated separators is
still a mathematical hypothesis.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {X E F Z H VB G : Type v}

/-- A locally controlled strict original-partial B-tree completion
relative to the EXACT original-core intersection in every full
embedded test on at most n vertices.

The anchor is allowed to have any fully embedded presentation, but
its range in Test must equal precisely those test vertices whose
images lie inside the original Core.  Its labels are forced by the
same distinguished original-core embedding.  It is not a weak
substructure enlarged by function closure. -/
def HasExactCoreAnchoredOriginalPartialCompletions
    (n : ℕ)
    (Base : Structure L VB)
    (Start : Structure L G)
    (Core : Structure L X)
    (Current : Structure L E)
    (coreIn : Embedding Core Current)
    (q : X → G) : Prop :=
  ∀ (U : Type v) [Finite U]
    (Test : Structure L U) (testIn : Embedding Test Current),
    Nat.card U ≤ n →
    ∃ (J : Type v) (Anchor : Structure L J)
      (anchor : Embedding Anchor Test)
      (toCore : Embedding Anchor Core),
      (∀ x : J, testIn (anchor x) = coreIn (toCore x)) ∧
      (∀ z : U,
        (∃ x : J, anchor x = z) ↔
        (∃ y : X, testIn z = coreIn y)) ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base anchor (q ∘ toCore)

namespace IsFreeAmalgam

/-- Binary preservation of the exact original-core-anchored strict
original-partial local completion property in the full function
language.

Assume the old current stage has the invariant for tests of at most
n vertices.  The copied-old side is attached along a full support
embedding through the distinguished original core.  For each bounded
test of the WHOLE free amalgam, require a strict copied-side relative
completion over the fixed original support labels on the actual
closed common separator.  Then the whole new stage retains the same
exact-core invariant.

The proof composes:
* the full closed-test pullback,
* exact old-core anchor extraction,
* transfer of a prior exact anchored completion to the canonical
  pulled-back anchor,
* the verified one-sided relative strict star attachment,
* and exact identification of the resulting anchor's range in the
  new whole test.

It does not require the common root to be irreducible, one-generated,
or injectively projected. The incoming right witness remains an
explicit hypothesis, not an unproved axiom hidden in the code. -/
theorem hasExactCoreAnchoredOriginalPartialCompletions_attach
    {Core : Structure L X}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L Z}
    {Root : Structure L H}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (Start : Structure L G)
    (n : ℕ)
    (coreIn : Embedding Core Left)
    (supportIn : Embedding Root Core)
    (hSupport : ∀ x : H, sL x = coreIn (supportIn x))
    (q : X → G)
    (hOld : HasExactCoreAnchoredOriginalPartialCompletions
      n Base Start Core Left coreIn q)
    (hCopy :
      ∀ (U : Type v) [Finite U]
        (Test : Structure L U) (testIn : Embedding Test Whole),
        Nat.card U ≤ n →
        let pb := hfree.embeddingPullback testIn
        HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base pb.toRight
          (q ∘ supportIn ∘ pb.commonMap)) :
    HasExactCoreAnchoredOriginalPartialCompletions
      n Base Start Core Whole (iL.comp coreIn) q := by
  intro U _ Test testIn hCard
  let pb := hfree.embeddingPullback testIn
  letI : Finite pb.Left :=
    Finite.of_injective pb.leftIn pb.leftIn.injective
  have hLeftCard : Nat.card pb.Left ≤ n :=
    (Nat.card_le_card_of_injective
      pb.leftIn pb.leftIn.injective).trans hCard
  obtain ⟨JOld, OldAnchor, oldIn, oldToCore,
    hOldComm, hOldExact, hOldRel⟩ :=
    hOld pb.Left pb.left pb.leftMap hLeftCard
  obtain ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap⟩ :=
    EmbeddingPullback.common_factors_through_closed_anchor_with_map
      hfree testIn pb Core coreIn supportIn hSupport
  have hLeft : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base
      (inclusion pb.left T hT) (q ∘ toOriginal) :=
    HasOriginalPartialTreeExtensionCompletion.of_exact_anchor_range
      Base oldIn (inclusion pb.left T hT)
      oldToCore toOriginal pb.leftMap coreIn q
      hOldComm hMap hOldExact hOldRel
  have hSelected : ∀ x : pb.Common,
      toOriginal (rootInAnchor x) = supportIn (pb.commonMap x) := by
    intro x
    apply coreIn.injective
    calc
      coreIn (toOriginal (rootInAnchor x)) =
          pb.leftMap ((inclusion pb.left T hT) (rootInAnchor x)) :=
        (hMap (rootInAnchor x)).symm
      _ = pb.leftMap (pb.toLeft x) :=
        congrArg pb.leftMap (hRoot x)
      _ = sL (pb.commonMap x) := pb.common_left x
      _ = coreIn (supportIn (pb.commonMap x)) := hSupport (pb.commonMap x)
  have hRootMaps :
      ((q ∘ toOriginal) ∘ rootInAnchor) =
        (q ∘ supportIn ∘ pb.commonMap) := by
    funext x
    exact congrArg q (hSelected x)
  have hCopyRelative : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base pb.toRight
      ((q ∘ toOriginal) ∘ rootInAnchor) := by
    rw [hRootMaps]
    exact hCopy U Test testIn hCard
  have hNewRel : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base
      (pb.leftIn.comp (inclusion pb.left T hT))
      (q ∘ toOriginal) :=
    pb.free.originalPartialTreeExtension_append_over_anchor
      Base Start (inclusion pb.left T hT) (q ∘ toOriginal)
      rootInAnchor (fun x => (hRoot x).symm)
      hLeft hCopyRelative
  have hNewComm : ∀ x : T,
      testIn ((pb.leftIn.comp (inclusion pb.left T hT)) x) =
        (iL.comp coreIn) (toOriginal x) := by
    intro x
    calc
      testIn ((pb.leftIn.comp (inclusion pb.left T hT)) x) =
          iL (pb.leftMap ((inclusion pb.left T hT) x)) :=
        pb.left_factor ((inclusion pb.left T hT) x)
      _ = iL (coreIn (toOriginal x)) := congrArg iL (hMap x)
      _ = (iL.comp coreIn) (toOriginal x) := rfl
  have hNewExact : ∀ z : U,
      (∃ x : T, (pb.leftIn.comp (inclusion pb.left T hT)) x = z) ↔
      (∃ y : X, testIn z = (iL.comp coreIn) y) :=
    EmbeddingPullback.left_original_anchor_exact_range
      hfree testIn pb Core coreIn T hT hExact
  exact ⟨T, pb.left.induce T hT,
    pb.leftIn.comp (inclusion pb.left T hT),
    toOriginal, hNewComm, hNewExact, hNewRel⟩

end IsFreeAmalgam
end StructuralRamsey.Structure

import PartiteConstruction.Functional.NativeClosedPullbackAnchorFactor
import PartiteConstruction.Functional.OriginalPartialAnchorRestriction

/-!
# Exact mapped Hales--Jewett anchor in functional closed tests

The published 2019 Picture induction attaches old-stage copies to one
distinguished functional Hales--Jewett power.  The intersection of a
closed test with the old core must be taken EXACTLY, without closing a
weak vertex subset and increasing the rank budget.

Previously the full common test separator was known to lie in the
tested original core.  Here its intersection is equipped also with
the FULL embedding back to the distinguished original core.  This
makes the old A-support labels a genuine fixed root map, rather than
an arbitrary completion chosen after each successive attachment.

The final native lemma combines this mapped geometry with the verified
original-partial strict star-extension theorem.  The left-side anchored
completion and the new copied-side relative witness remain hypotheses:
the uniform latter existence for mixed multi-generated separators is
not known.  No total-fibre projection is asserted.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C U J : Type v}
variable {Dsrc : Structure L H}
variable {Esrc : Structure L E}
variable {Fsrc : Structure L F}
variable {Csrc : Structure L C}
variable {TestSrc : Structure L U}
variable {sE : Embedding Dsrc Esrc}
variable {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc}
variable {iF : Embedding Fsrc Csrc}

/-- A full closed test of a functional free amalgam has a distinguished
closed anchor given by its EXACT intersection with the original core.
The common separator embeds into the tested anchor, which itself
embeds FULLY into the original core.  Both commuting triangles are
literal source-embedding equalities; the common-root labels therefore
have no independent choices or extra closure vertices. -/
theorem EmbeddingPullback.common_factors_through_closed_anchor_with_map
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding TestSrc Csrc)
    (pb : EmbeddingPullback hfree e)
    (Anchor : Structure L J)
    (j : Embedding Anchor Esrc)
    (a : Embedding Dsrc Anchor)
    (hSupport : ∀ d : H, sE d = j (a d)) :
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Embedding pb.common (pb.left.induce T hT))
      (toOriginal : Embedding (pb.left.induce T hT) Anchor),
      T = {x | pb.leftMap x ∈ Set.range j} ∧
      (∀ x : pb.Common,
        (inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x) ∧
      (∀ x : T,
        pb.leftMap ((inclusion pb.left T hT) x) = j (toOriginal x)) := by
  classical
  let T : Set pb.Left := {x | pb.leftMap x ∈ Set.range j}
  have hT : pb.left.IsClosed T :=
    pb.leftMap.preimage_isClosed (Set.range j) j.range_isClosed
  let iT : Embedding (pb.left.induce T hT) pb.left :=
    inclusion pb.left T hT
  have hAnchorRange :
      ∀ x : T, ∃ y : J, pb.leftMap (iT x) = j y := by
    intro x
    exact x.2
  let toOriginal : Embedding (pb.left.induce T hT) Anchor :=
    (pb.leftMap.comp iT).factorThroughRange j hAnchorRange
  have hCommonRange :
      ∀ x : pb.Common, ∃ y : T, pb.toLeft x = iT y := by
    intro x
    refine ⟨⟨pb.toLeft x, ?_⟩, rfl⟩
    change pb.leftMap (pb.toLeft x) ∈ Set.range j
    rw [pb.common_left x, hSupport (pb.commonMap x)]
    exact ⟨a (pb.commonMap x), rfl⟩
  let rootInAnchor : Embedding pb.common (pb.left.induce T hT) :=
    pb.toLeft.factorThroughRange iT hCommonRange
  refine ⟨T, hT, rootInAnchor, toOriginal, rfl, ?_, ?_⟩
  · intro x
    exact (Classical.choose_spec (hCommonRange x)).symm
  · intro x
    exact Classical.choose_spec (hAnchorRange x)

end StructuralRamsey.Structure.IsFreeAmalgam


namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W X VB G : Type v}

/-- The mapped closed power-core intersection in the ACTUAL native
one-copy attachment UnitAttachD, not an abstract U-closed surrogate.
This is the geometric interface for all later attachments to the
original Hales--Jewett power: the old support embedding factors as
coreIn composed with the prescribed support embedding. -/
theorem closedTestPullback_common_in_original_core_with_map
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (OriginalCore : Structure L X)
    (coreIn : Structure.Embedding OriginalCore D.toStructure)
    (supportIn : Structure.Embedding
      (B.induce S hS).toStructure OriginalCore)
    (hFactor : ∀ s : S, f.toEmbedding s = coreIn (supportIn s))
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test) :
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Structure.Embedding pb.common (pb.left.induce T hT))
      (toOriginal : Structure.Embedding
        (pb.left.induce T hT) OriginalCore),
      T = {x | pb.leftMap x ∈ Set.range coreIn} ∧
      (∀ x : pb.Common,
        (Structure.inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x) ∧
      (∀ x : T,
        pb.leftMap ((Structure.inclusion pb.left T hT) x) =
          coreIn (toOriginal x)) := by
  exact Structure.IsFreeAmalgam.EmbeddingPullback
    .common_factors_through_closed_anchor_with_map
    (unit_isFreeAmalgam_full B S hS D f)
    (Structure.inclusion (UnitAttachD B S hS D f).toStructure Test hTest)
    (closedTestPullback B S hS D f Test hTest)
    OriginalCore coreIn supportIn hFactor

/-- The exact closed-test step in the published star-shaped Picture.

The two required relative witnesses concern:
(1) the ALREADY TESTED LEFT SIDE, anchored at its exact intersection
with the ORIGINAL core, and
(2) the NEW copied old-stage side, over the canonical restriction of
that SAME root map q.

If they exist, the completed WHOLE test remains anchored at the
original core intersection.  This preserves the inductive form
through successive old-copy attachments without changing the
function-closed vertex test.  The old-side witness for hard mixed
multi-generated roots is still an explicit premise. -/
theorem closedTest_originalPartial_star_step_over_original_core
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (OriginalCore : Structure L X)
    (coreIn : Structure.Embedding OriginalCore D.toStructure)
    (supportIn : Structure.Embedding
      (B.induce S hS).toStructure OriginalCore)
    (hFactor : ∀ s : S, f.toEmbedding s = coreIn (supportIn s))
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB) (Start : Structure L G)
    (q : X → G) :
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Structure.Embedding pb.common (pb.left.induce T hT))
      (toOriginal : Structure.Embedding
        (pb.left.induce T hT) OriginalCore),
      T = {x | pb.leftMap x ∈ Set.range coreIn} ∧
      (∀ x : pb.Common,
        (Structure.inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x) ∧
      (∀ x : T,
        pb.leftMap ((Structure.inclusion pb.left T hT) x) =
          coreIn (toOriginal x)) ∧
      (HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base (Structure.inclusion pb.left T hT)
          (q ∘ toOriginal) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base pb.toRight
          ((q ∘ toOriginal) ∘ rootInAnchor) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base
          (pb.leftIn.comp (Structure.inclusion pb.left T hT))
          (q ∘ toOriginal)) := by
  let pb := closedTestPullback B S hS D f Test hTest
  obtain ⟨T, hT, rootInAnchor, toOriginal, hExact, hRoot, hMap⟩ :=
    closedTestPullback_common_in_original_core_with_map
      B S hS D f OriginalCore coreIn supportIn hFactor Test hTest
  refine ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap, ?_⟩
  intro hLeft hCopy
  exact pb.free.originalPartialTreeExtension_append_over_anchor
    Base Start (Structure.inclusion pb.left T hT)
    (q ∘ toOriginal) rootInAnchor
    (fun x => (hRoot x).symm) hLeft hCopy

/-- If the entire previous Picture already has an anchored strict
original-partial completion, its closed tested left side obtains the
necessary local witness AUTOMATICALLY by full restriction.  The only
additional hypothesis is the new old-copy relative extension over
the canonical root in Start.

This stronger premise is useful for the first native power attachment
and its globally controlled variants.  It is NOT substituted for the
smaller-test induction hypothesis in later arbitrary Pictures. -/
theorem closedTest_originalPartial_star_step_from_global_anchor
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (OriginalCore : Structure L X)
    (coreIn : Structure.Embedding OriginalCore D.toStructure)
    (supportIn : Structure.Embedding
      (B.induce S hS).toStructure OriginalCore)
    (hFactor : ∀ s : S, f.toEmbedding s = coreIn (supportIn s))
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB) (Start : Structure L G)
    (q : X → G)
    (hPrior : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base coreIn q) :
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Structure.Embedding pb.common (pb.left.induce T hT))
      (toOriginal : Structure.Embedding
        (pb.left.induce T hT) OriginalCore),
      T = {x | pb.leftMap x ∈ Set.range coreIn} ∧
      (∀ x : pb.Common,
        (Structure.inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x) ∧
      (∀ x : T,
        pb.leftMap ((Structure.inclusion pb.left T hT) x) =
          coreIn (toOriginal x)) ∧
      (HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base pb.toRight
          ((q ∘ toOriginal) ∘ rootInAnchor) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base
          (pb.leftIn.comp (Structure.inclusion pb.left T hT))
          (q ∘ toOriginal)) := by
  let pb := closedTestPullback B S hS D f Test hTest
  obtain ⟨T, hT, rootInAnchor, toOriginal, hExact, hRoot, hMap, hStep⟩ :=
    closedTest_originalPartial_star_step_over_original_core
      B S hS D f OriginalCore coreIn supportIn hFactor
      Test hTest Base Start q
  refine ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap, ?_⟩
  intro hCopy
  apply hStep
  · exact HasOriginalPartialTreeExtensionCompletion.restrict_to_pulled_anchor
      Base coreIn q hPrior pb.leftMap
      (Structure.inclusion pb.left T hT) toOriginal hMap
  · exact hCopy

end StructuralRamsey.FunctionalPartite.Attachment

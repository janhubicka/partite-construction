import PartiteConstruction.Functional.NativeCanonicalSupportStarStep

/-!
# The old Hales--Jewett anchor is exactly the original-core intersection

For the published full-functional Picture induction it is not enough to
know that the common separator *factors* through the original power core.
After one attachment, the next test must still use the *same* original
core, and its anchor must consist of exactly the tested vertices in
that core, with no generated closure and no chosen extra vertices.

The generic lemma below proves that fact for any full functional
free-amalgam pullback. The native corollary identifies the anchor in
the actual UnitAttachD test AND preserves the conditional strict
original-2019 partial-function star step from the previous module.
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

/-- The exact preimage of an original embedded LEFT core in a closed
full-functional test is the image of the tested-left intersection with
that core.  This remains true for points presented on the RIGHT source
side: the free-amalgam overlap and the pullback's right reflection
force them into the actual shared separator.

This lemma does not require the attaching root to be irreducible or
the original-core image to be injectively projected into a B-tree.
All displayed maps are FULL structure embeddings. -/
theorem EmbeddingPullback.left_original_anchor_exact_range
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding TestSrc Csrc)
    (pb : EmbeddingPullback hfree e)
    (Anchor : Structure L J)
    (j : Embedding Anchor Esrc)
    (T : Set pb.Left)
    (hT : pb.left.IsClosed T)
    (hExact : T = {x | pb.leftMap x ∈ Set.range j}) :
    ∀ z : U,
      (∃ x : T,
        (pb.leftIn.comp (inclusion pb.left T hT)) x = z) ↔
      (∃ a : J, e z = iE (j a)) := by
  classical
  intro z
  constructor
  · rintro ⟨x, hx⟩
    have hxMem : pb.leftMap ((inclusion pb.left T hT) x) ∈ Set.range j := by
      change pb.leftMap x.1 ∈ Set.range j
      have hm : x.1 ∈ T := x.2
      rw [hExact] at hm
      exact hm
    obtain ⟨a, ha⟩ := hxMem
    refine ⟨a, ?_⟩
    calc
      e z = e (pb.leftIn ((inclusion pb.left T hT) x)) :=
        congrArg e hx.symm
      _ = iE (pb.leftMap ((inclusion pb.left T hT) x)) :=
        pb.left_factor ((inclusion pb.left T hT) x)
      _ = iE (j a) := congrArg iE ha.symm
  · rintro ⟨a, hza⟩
    rcases pb.free.covers z with ⟨b, hzb⟩ | ⟨c, hzc⟩
    · have hbMap : pb.leftMap b = j a := by
        apply iE.injective
        calc
          iE (pb.leftMap b) = e (pb.leftIn b) :=
            (pb.left_factor b).symm
          _ = e z := congrArg e hzb.symm
          _ = iE (j a) := hza
      have hbT : b ∈ T := by
        rw [hExact]
        exact ⟨a, hbMap.symm⟩
      refine ⟨⟨b, hbT⟩, ?_⟩
      change pb.leftIn b = z
      exact hzb.symm
    · have hCross : iE (j a) = iF (pb.rightMap c) := by
        calc
          iE (j a) = e z := hza.symm
          _ = e (pb.rightIn c) := congrArg e hzc
          _ = iF (pb.rightMap c) := pb.right_factor c
      obtain ⟨d, hdL, hdR⟩ :=
        (hfree.overlap (j a) (pb.rightMap c)).mp hCross
      obtain ⟨x, hcx, hdx⟩ := pb.right_reflect c d hdR
      have hxT : pb.toLeft x ∈ T := by
        rw [hExact]
        refine ⟨a, ?_⟩
        calc
          j a = sE d := hdL.symm
          _ = sE (pb.commonMap x) := congrArg sE hdx.symm
          _ = pb.leftMap (pb.toLeft x) := (pb.common_left x).symm
      refine ⟨⟨pb.toLeft x, hxT⟩, ?_⟩
      change pb.leftIn (pb.toLeft x) = z
      calc
        pb.leftIn (pb.toLeft x) = pb.rightIn (pb.toRight x) :=
          (pb.free.overlap (pb.toLeft x) (pb.toRight x)).mpr
            ⟨x, rfl, rfl⟩
        _ = pb.rightIn c := congrArg pb.rightIn hcx.symm
        _ = z := hzc.symm

end StructuralRamsey.Structure.IsFreeAmalgam

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W X VB G : Type v}

/-- The whole-test old HJ anchor is EXACTLY the original-core
intersection in the native full-functional binary attachment,
not merely a witness containing the common separator.

Moreover, the original selected-support map agrees exactly on
the common separator; and the next old-copy attachment preserves
a strict relative original-2019 partial completion provided its
two canonical compatible side witnesses exist.

The hard multi-generated copied-side relative extension remains
a hypothesis, not a claim of this theorem. -/
theorem closedTest_originalPartial_star_step_exact_whole_anchor
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
      (∀ x : pb.Common,
        toOriginal (rootInAnchor x) = supportIn (pb.commonMap x)) ∧
      (∀ z : Test,
        (∃ x : T,
          (pb.leftIn.comp (Structure.inclusion pb.left T hT)) x = z) ↔
        (∃ a : X,
          (Structure.inclusion
            (UnitAttachD B S hS D f).toStructure Test hTest) z =
            (unitCoreEmbedding B S hS D f) (coreIn a))) ∧
      (HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base (Structure.inclusion pb.left T hT)
          (q ∘ toOriginal) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base pb.toRight
          (q ∘ supportIn ∘ pb.commonMap) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base
          (pb.leftIn.comp (Structure.inclusion pb.left T hT))
          (q ∘ toOriginal)) := by
  let pb := closedTestPullback B S hS D f Test hTest
  obtain ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap, hSelected, hStep⟩ :=
    closedTest_originalPartial_star_step_with_selected_support
      B S hS D f OriginalCore coreIn supportIn hFactor
      Test hTest Base Start q
  have hWhole :
      ∀ z : Test,
        (∃ x : T,
          (pb.leftIn.comp (Structure.inclusion pb.left T hT)) x = z) ↔
        (∃ a : X,
          (Structure.inclusion
            (UnitAttachD B S hS D f).toStructure Test hTest) z =
            (unitCoreEmbedding B S hS D f) (coreIn a)) :=
    Structure.IsFreeAmalgam.EmbeddingPullback.left_original_anchor_exact_range
      (unit_isFreeAmalgam_full B S hS D f)
      (Structure.inclusion (UnitAttachD B S hS D f).toStructure Test hTest)
      pb OriginalCore coreIn T hT hExact
  exact ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap, hSelected, hWhole, hStep⟩

end StructuralRamsey.FunctionalPartite.Attachment

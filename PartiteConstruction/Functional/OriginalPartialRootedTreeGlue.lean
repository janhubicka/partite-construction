import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.FullFreeAmalgam
import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-!
# Strict full-functional B-tree gluing under ORIGINAL partial maps

The published mixed partite argument needs to glue two B-tree completions
of proper pieces. Their common source root can be reducible; merely having
two independent partial homomorphism-embeddings into B-trees does not allow
gluing, since the restrictions to the root may not be embeddings.

Here we prove the exact sufficient *rooted* version. Suppose each side
has an EHN (original-partial) homomorphism-embedding into a genuine
strict full-functional B-tree, whose root restriction is a specified full
embedding into a constituent irreducible piece. Then free-amalgamate the
TWO TARGET TREES over the common full root and combine the source maps.
This gives an original-partial HE into a strict tree, without requiring
root isolation of the source side maps. Cross-side map collisions are
permitted in the original 2019 partial-HE convention; the source
irreducibles localise to one side of its free amalgam.

This theorem is a conditional compatibility lemma, NOT the existence
of compatible rooted completions for arbitrary mixed native tests.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F Z VB VL VR : Type v}

/-- Rooted strict B-tree amalgamation for EHN/original-partial maps.

The source common root may be reducible. What is needed is a FULL root
embedding into each side B-tree, contained in an irreducible B-piece,
and agreement of the side maps with those prescribed embeddings.
No root isolation or global injection of the source maps is assumed. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_glue_rooted
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSource : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (TL : Structure L VL) (TR : Structure L VR)
    (hTL : TreeAmalgam Base VL TL)
    (hTR : TreeAmalgam Base VR TR)
    (rootL : Embedding Root TL) (rootR : Embedding Root TR)
    (hRootL : rootL.ContainedInIrreducible)
    (hRootR : rootR.ContainedInIrreducible)
    (pL : E → VL) (pR : F → VR)
    (hpL : Left.IsEHNHomomorphismEmbedding TL pL)
    (hpR : Right.IsEHNHomomorphismEmbedding TR pR)
    (hLiftL : ∀ x : H, pL (sL x) = rootL x)
    (hLiftR : ∀ x : H, pR (sR x) = rootR x) :
    HasOriginalPartialTreeCompletion Base Whole := by
  let Target := FreeAmalgam.amalgam Root TL TR rootL rootR
  let jL := FreeAmalgam.leftEmbedding Root TL TR rootL rootR
  let jR := FreeAmalgam.rightEmbedding Root TL TR rootL rootR
  have hTarget : IsFreeAmalgam rootL rootR jL jR :=
    FreeAmalgam.isFreeAmalgam Root TL TR rootL rootR
  have hTree : TreeAmalgam Base _ Target :=
    TreeAmalgam.glue hTL hTR rootL rootR hRootL hRootR
      jL jR hTarget
  have hMapL : Left.IsEHNHomomorphismEmbedding Target (jL ∘ pL) :=
    jL.isEHNHomomorphismEmbedding.comp hpL
  have hMapR : Right.IsEHNHomomorphismEmbedding Target (jR ∘ pR) :=
    jR.isEHNHomomorphismEmbedding.comp hpR
  have hMatch : ∀ x : H,
      (jL ∘ pL) (sL x) = (jR ∘ pR) (sR x) := by
    intro x
    change jL (pL (sL x)) = jR (pR (sR x))
    rw [hLiftL x, hLiftR x]
    exact (hTarget.overlap (rootL x) (rootR x)).mpr
      ⟨x, rfl, rfl⟩
  obtain ⟨p, hp, _hL, _hR⟩ :=
    hSource.exists_EHN_projection
      (jL ∘ pL) (jR ∘ pR) hMapL hMapR hMatch
  exact ⟨_, Target, hTree, p, hp.toOriginalPartial⟩


/-- The reducible-root form closer to the actual 2019 mixed induction.

The common root is first completed by a possibly NONINJECTIVE original
partial map q into a genuine strict B-tree Start. The two side witnesses
need only be EHN maps into strict *tree extensions of this same Start*,
whose root maps agree with q after the canonical start embeddings.
No root isolation or full-fibre reflection is required to combine these
maps. The merge of the two target extensions is still a genuine strict
functional B-tree.

The remaining geometric step is to obtain these compatible side
extensions from the smaller-test predecessor hypothesis. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_glue_commonTree
    {G : Type v} {Start : Structure L G}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSource : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (hStart : TreeAmalgam Base G Start)
    (q : H → G)
    (TL : Structure L VL) (TR : Structure L VR)
    (hExtL : TreeExtension Base Start VL TL)
    (hExtR : TreeExtension Base Start VR TR)
    (pL : E → VL) (pR : F → VR)
    (hpL : Left.IsEHNHomomorphismEmbedding TL pL)
    (hpR : Right.IsEHNHomomorphismEmbedding TR pR)
    (hLiftL : ∀ x : H,
      pL (sL x) = hExtL.startEmbedding (q x))
    (hLiftR : ∀ x : H,
      pR (sR x) = hExtR.startEmbedding (q x)) :
    HasOriginalPartialTreeCompletion Base Whole := by
  obtain ⟨G2, Target, hAll, eL, eR, _hFree, hStartL, hStartR⟩ :=
    hExtL.mergeFree hExtR
  have hTree : TreeAmalgam Base G2 Target := hAll.toTree hStart
  have hMapL : Left.IsEHNHomomorphismEmbedding Target (eL ∘ pL) :=
    eL.isEHNHomomorphismEmbedding.comp hpL
  have hMapR : Right.IsEHNHomomorphismEmbedding Target (eR ∘ pR) :=
    eR.isEHNHomomorphismEmbedding.comp hpR
  have hAgree : ∀ x : H,
      (eL ∘ pL) (sL x) = (eR ∘ pR) (sR x) := by
    intro x
    change eL (pL (sL x)) = eR (pR (sR x))
    rw [hLiftL x, hLiftR x]
    exact (hStartL (q x)).trans (hStartR (q x)).symm
  obtain ⟨p, hp, _hl, _hr⟩ :=
    hSource.exists_EHN_projection
      (eL ∘ pL) (eR ∘ pR) hMapL hMapR hAgree
  exact ⟨G2, Target, hTree, p, hp.toOriginalPartial⟩



/-- A side has a strict full-functional B-tree completion RELATIVE to
a fixed strict completed common root, in the original 2019 partial-HE
semantics. Unlike the total-fibre version, there is NO artificial
root-isolation condition. The root map q may be noninjective. -/
def HasOriginalPartialTreeExtensionCompletion
    {G : Type v} {Start : Structure L G}
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (s : Embedding Root Side) (q : H → G) : Prop :=
  ∃ (Y : Type v) (Target : Structure L Y)
    (hExt : TreeExtension Base Start Y Target)
    (p : E → Y),
      IsOriginalPartialHomomorphismEmbedding Side Target p ∧
      ∀ x : H, p (s x) = hExt.startEmbedding (q x)

/-- Two original-partial strict side completions over the SAME strict
possibly reducible root tree glue to an original-partial strict
completion of the free source amalgam. The proof merely composes
the checked 2019-to-EHN semantic equivalence with the concrete
strict TreeExtension.mergeFree argument. No separate root-isolation
axiom is needed. -/
theorem IsFreeAmalgam.originalPartialTreeCompletion_glue_relative
    {G : Type v} {Start : Structure L G}
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB)
    (hStart : TreeAmalgam Base G Start)
    (q : H → G)
    (hL : HasOriginalPartialTreeExtensionCompletion Base sL q)
    (hR : HasOriginalPartialTreeExtensionCompletion Base sR q) :
    HasOriginalPartialTreeCompletion Base Whole := by
  obtain ⟨YL, TL, hExtL, pL, hpL, hcL⟩ := hL
  obtain ⟨YR, TR, hExtR, pR, hpR, hcR⟩ := hR
  exact hSrc.originalPartialTreeCompletion_glue_commonTree
    Base hStart q TL TR hExtL hExtR pL pR
    hpL.toEHN hpR.toEHN hcL hcR


end StructuralRamsey.Structure


namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W VB YL YR : Type v}

/-- Apply the original-partial strict rooted-tree gluing theorem to the
ACTUAL closed test in a genuine native binary EHN attachment.

The exact full-functional pullback provides the two side embeddings
and the common root. The two side target trees and their full embedded
root are inputs; their compatibility cannot be replaced by unrelated
unrooted local completions. This isolates the one remaining mixed case
of the published two-case iteration without adding closure vertices. -/
theorem closedTest_originalPartial_strictTree_of_rooted_sideCompletions
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB)
    (TL : Structure L YL) (TR : Structure L YR)
    (hTL : TreeAmalgam Base YL TL)
    (hTR : TreeAmalgam Base YR TR)
    (rootL : Structure.Embedding
      (closedTestPullback B S hS D f Test hTest).common TL)
    (rootR : Structure.Embedding
      (closedTestPullback B S hS D f Test hTest).common TR)
    (hRootL : rootL.ContainedInIrreducible)
    (hRootR : rootR.ContainedInIrreducible)
    (pL : (closedTestPullback B S hS D f Test hTest).Left → YL)
    (pR : (closedTestPullback B S hS D f Test hTest).Right → YR)
    (hL : ((closedTestPullback B S hS D f Test hTest).left)
        .IsEHNHomomorphismEmbedding TL pL)
    (hR : ((closedTestPullback B S hS D f Test hTest).right)
        .IsEHNHomomorphismEmbedding TR pR)
    (hLiftL : ∀ x : (closedTestPullback B S hS D f Test hTest).Common,
      pL ((closedTestPullback B S hS D f Test hTest).toLeft x) = rootL x)
    (hLiftR : ∀ x : (closedTestPullback B S hS D f Test hTest).Common,
      pR ((closedTestPullback B S hS D f Test hTest).toRight x) = rootR x) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B S hS D f).toStructure.induce Test hTest) := by
  let pb := closedTestPullback B S hS D f Test hTest
  exact pb.free.originalPartialTreeCompletion_glue_rooted Base
    TL TR hTL hTR rootL rootR hRootL hRootR
    pL pR hL hR hLiftL hLiftR


/-- Actual native mixed test over a REDUCIBLE common separator.

Start is a strict B-tree completion of the common separator, and q is
its (possibly noninjective) original-partial completion map. Each
proper tested side must have an EHN completion into a STRICT
extension of this SAME Start, agreeing on q. The abstract mergeFree
lemma then supplies one strict full-functional B-tree completion of
the original exact closed test.

This is a conditional formulation of the remaining mathematical
obligation in the published two-case induction. It no longer needs
root isolation for the original-partial homomorphism notion, but it
still needs existence of compatible strict side extensions. -/
theorem closedTest_originalPartial_strictTree_of_commonTreeExtensions
    {G : Type v}
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB)
    (Start : Structure L G)
    (hStart : TreeAmalgam Base G Start)
    (q : (closedTestPullback B S hS D f Test hTest).Common → G)
    (TL : Structure L YL) (TR : Structure L YR)
    (hExtL : TreeExtension Base Start YL TL)
    (hExtR : TreeExtension Base Start YR TR)
    (pL : (closedTestPullback B S hS D f Test hTest).Left → YL)
    (pR : (closedTestPullback B S hS D f Test hTest).Right → YR)
    (hL : ((closedTestPullback B S hS D f Test hTest).left)
      .IsEHNHomomorphismEmbedding TL pL)
    (hR : ((closedTestPullback B S hS D f Test hTest).right)
      .IsEHNHomomorphismEmbedding TR pR)
    (hLiftL : ∀ x : (closedTestPullback B S hS D f Test hTest).Common,
      pL ((closedTestPullback B S hS D f Test hTest).toLeft x)
        = hExtL.startEmbedding (q x))
    (hLiftR : ∀ x : (closedTestPullback B S hS D f Test hTest).Common,
      pR ((closedTestPullback B S hS D f Test hTest).toRight x)
        = hExtR.startEmbedding (q x)) :
    HasOriginalPartialTreeCompletion Base
      ((UnitAttachD B S hS D f).toStructure.induce Test hTest) := by
  let pb := closedTestPullback B S hS D f Test hTest
  exact pb.free.originalPartialTreeCompletion_glue_commonTree
    Base hStart q TL TR hExtL hExtR pL pR hL hR hLiftL hLiftR

end StructuralRamsey.FunctionalPartite.Attachment

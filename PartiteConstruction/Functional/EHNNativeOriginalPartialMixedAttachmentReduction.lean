import PartiteConstruction.Functional.OriginalPartialSmallImageGeneratorHull
import PartiteConstruction.Functional.OriginalPartialRootedTreeGlue
import PartiteConstruction.Functional.EHNClosedAttachmentRootHistory

/-!
# Exact mixed-only missing lemma for strict native functional attachment

An actual native EHN binary attachment is a FULL functional free
amalgam of the new Hales--Jewett core and one attached old B-picture
copy over a closed selected A-support.

At generator rank n, every CLOSED test in that attachment either:
  (a) lies entirely in the new core;
  (b) lies entirely in the attached old copy; or
  (c) genuinely meets both exterior sides.

In (a) and (b), the strict original-partial n-generator invariant of
that full side already gives the target by factoring the exact TEST's
full inclusion through the constituent side embedding. No closure
hull or extra source vertex is introduced.

For (c), the only needed new information is a pair of strict
original-partial relative completions over the SAME completed common
separator. The reducible common separator and partial root map are
allowed. Their gluing is already proved in PR #277 and is invoked here.

Thus preserving generator-rank strict local trees through an actual
functional binary attachment is reduced to the MIXED ROOTED EXTENSION
lemma below. This is deliberately conditional and must not be called
an unconditional proof of the published strict functional theorem.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

noncomputable section
universe u v
variable {L : Language.{u}}
variable {P V W VB : Type v}

/-- Native mixed-root relative completion request at generator rank n.

All source tests are genuinely CLOSED substructures on their EXACT
carrier. The common root is the actual canonical full-functional
pullback of the attachment. No abstract independently chosen overlap
is permitted. The common completion may be a tree, not one B-copy. -/
def NativeMixedOriginalPartialRelativeExtension
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Base : Structure L VB) (n : ℕ) : Prop :=
  ∀ (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (hGen : ((UnitAttachD B S hS D f).toStructure.induce
      Test hTest).GeneratedByAtMost n)
    (hOutsideCore : ¬ ∀ x : Test, ∃ w : W,
      x.1 = unitCoreEmbedding B S hS D f w)
    (hOutsideCopy : ¬ ∀ x : Test, ∃ v : V,
      x.1 = unitCopyEmbedding B S hS D f v),
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
      TreeAmalgam Base G Start ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toLeft q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toRight q

/-- Exact pure/mixed trichotomy for the ACTUAL functional binary
attachment, with the PURE cases discharged from the two already
established rank-n side invariants. Strict gluing handles a reducible
mixed root under the one explicit relative-extension hypothesis. -/
theorem nativeAttach_generatorRank_of_mixed_relative_extensions
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Base : Structure L VB) (n : ℕ)
    (hCore : LocallyGeneratedOriginalPartialTreeCompletable
      Base D.toStructure n)
    (hCopy : LocallyGeneratedOriginalPartialTreeCompletable
      Base B.toStructure n)
    (hMixed : NativeMixedOriginalPartialRelativeExtension
      B S hS D f Base n) :
    LocallyGeneratedOriginalPartialTreeCompletable
      Base (UnitAttachD B S hS D f).toStructure n := by
  intro Test hTest hGen
  let Whole := (UnitAttachD B S hS D f).toStructure
  let Small := Whole.induce Test hTest
  let inc : Embedding Small Whole := inclusion Whole Test hTest
  let iCore : Embedding D.toStructure Whole :=
    unitCoreEmbedding B S hS D f
  let iCopy : Embedding B.toStructure Whole :=
    unitCopyEmbedding B S hS D f
  by_cases hInCore : ∀ x : Test, ∃ w : W, inc x = iCore w
  · let eCore : Embedding Small D.toStructure :=
      inc.factorThroughRange iCore hInCore
    exact hCore.completion_of_embedding Small hGen eCore
  · by_cases hInCopy : ∀ x : Test, ∃ v : V, inc x = iCopy v
    · let eCopy : Embedding Small B.toStructure :=
        inc.factorThroughRange iCopy hInCopy
      exact hCopy.completion_of_embedding Small hGen eCopy
    · let pb := closedTestPullback B S hS D f Test hTest
      obtain ⟨G, Start, q, hStart, hLeft, hRight⟩ :=
        hMixed Test hTest hGen hInCore hInCopy
      exact pb.free.originalPartialTreeCompletion_glue_relative
        Base hStart q hLeft hRight

end
end StructuralRamsey.FunctionalPartite.Attachment

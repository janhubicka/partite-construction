import PartiteConstruction.Functional.EHNNativeOriginalPartialMixedAttachmentReduction

/-!
# Maximal projected generator support: the ONLY hard native mixed case

The published Picture induction splits by the size of a projected
weak vertex test. For genuine function structures and strict
ORIGINAL-PARTIAL tree targets, the sound strengthened induction
instead counts generators of the CLOSED source test.

A source test with at most n generators projects into the same
n-generator bound. If its projected generating set has fewer
than n distinct parts, strict completion transfers through the
closed HULL of those parts using the predecessor rank-(n-1)
invariant. The hull may have arbitrarily many vertices.

If projection has exactly n distinct generator values, the test
is genuinely maximal. PURE core and PURE old-copy tests are
already handled by the respective rank-n invariants. The only
new obligation is then: for each maximal genuinely MIXED test,
build two strict original-partial relative B-tree completions
over one same completion of its actual common separator.

This is conditional on that explicit maximal-mixed extension
property. It is NOT a proof that such extensions always exist.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure
noncomputable section
universe u v
variable {L : Language.{u}}
variable {P V W VB : Type v}
variable [DecidableEq P]

/-- Rooted completion requests only for genuine mixed closed tests
whose selected generating support has MAXIMAL projected rank n.
For lower projected rank the global predecessor strict invariant
already gives a completion, with no root-extension oracle. -/
def NativeMaximalMixedOriginalPartialRelativeExtension
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Base : Structure L VB) (n : ℕ) : Prop :=
  ∀ (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (G : Finset Test)
    (hGen : ((UnitAttachD B S hS D f).toStructure.induce
      Test hTest).GeneratedBy (↑G : Set Test))
    (hCard : G.card ≤ n)
    (hImage : (G.image
      (fun x : Test => (UnitAttachD B S hS D f).part x.1)).card = n)
    (hOutsideCore : ¬ ∀ x : Test, ∃ w : W,
      x.1 = unitCoreEmbedding B S hS D f w)
    (hOutsideCopy : ¬ ∀ x : Test, ∃ v : V,
      x.1 = unitCopyEmbedding B S hS D f v),
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (G₀ : Type v) (Start : Structure L G₀) (q : pb.Common → G₀),
      TreeAmalgam Base G₀ Start ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toLeft q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toRight q

/-- Exact *three-way* induction through one actual native full-function
binary attachment:
  1. pure core and pure old-copy tests use previous rank-n invariants;
  2. mixed tests with fewer than n projected generators use the
     predecessor rank-(n-1) invariant and closure-image rank transfer;
  3. only maximal-rank mixed tests need compatible strict root extensions.

In particular, no all-weak-tests strict completion axiom, no
bounded cardinality of generated hulls, and no root-isolation
assumption on original-partial maps are introduced. -/
theorem nativeAttach_generatorRank_of_maximal_mixed_extensions
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Outer : Structure L P)
    (hPart : (UnitAttachD B S hS D f).WeaklyPartiteOver Outer)
    (Base : Structure L VB) (n : ℕ)
    (hOldRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Outer (n - 1))
    (hCore : LocallyGeneratedOriginalPartialTreeCompletable
      Base D.toStructure n)
    (hCopy : LocallyGeneratedOriginalPartialTreeCompletable
      Base B.toStructure n)
    (hMixed : NativeMaximalMixedOriginalPartialRelativeExtension
      B S hS D f Base n) :
    LocallyGeneratedOriginalPartialTreeCompletable
      Base (UnitAttachD B S hS D f).toStructure n := by
  classical
  intro Test hTest hGen
  let C := UnitAttachD B S hS D f
  let Whole := C.toStructure
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
    · obtain ⟨G, hCard, hGGen⟩ := hGen
      let pSmall : Test → P := C.part ∘ Subtype.val
      have hSmallEHN : Small.IsEHNHomomorphismEmbedding Outer pSmall :=
        hPart.comp inc.isEHNHomomorphismEmbedding
      have hImageBound : (G.image pSmall).card ≤ n :=
        (Finset.card_image_le).trans hCard
      rcases lt_or_eq_of_le hImageBound with hDrop | hMax
      · exact HasOriginalPartialTreeCompletion.of_EHN_generator_image_drop
          hSmallEHN G hGGen n hDrop hOldRank
      · let pb := closedTestPullback B S hS D f Test hTest
        obtain ⟨G₀, Start, q, hStart, hLeft, hRight⟩ :=
          hMixed Test hTest G hGGen hCard hMax hInCore hInCopy
        exact pb.free.originalPartialTreeCompletion_glue_relative
          Base hStart q hLeft hRight

end
end StructuralRamsey.FunctionalPartite.Attachment

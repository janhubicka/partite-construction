import PartiteConstruction.Functional.OriginalPartialExactCoreLocalStep
import PartiteConstruction.Functional.EHNPowerOneSidedOriginalPartialMixedRoot

/-!
# Exact-root strict functional local completion of the initial HJ power

The original 2019 functional Picture starts from a genuine
Hales--Jewett power whose weak part projection to selected A,
followed by A ↪ Base, is an EHN/original-partial homomorphism-
embedding to one full Base copy.

When the whole current stage IS the distinguished original core,
the exact tested-core anchor of any full embedded test is simply the
entire test.  Thus its prescribed strict relative completion needs
zero tree attachments.  This proves the initial case of the exact
core-anchored local invariant used in the conditional binary
Picture step, at every vertex bound n.

No weak test has been given a full target completion here: the tests
in the exact-core invariant are FULL function-language embeddings,
so their function images are already present.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {X VB : Type v}

/-- If an entire original core EHN-projects into the strict starting
Base copy, EVERY fully embedded closed test is its own exact
original-core anchor and admits a strict original-2019 partial
relative completion over Base with no fresh B-copy attachment.

The proof does not require injectivity of the EHN projection, root
irreducibility or an upper bound on the function-closure size. -/
theorem HasExactCoreAnchoredOriginalPartialCompletions.of_core_EHN
    (n : ℕ)
    (Core : Structure L X)
    (Base : Structure L VB)
    (q : X → VB)
    (hq : Core.IsEHNHomomorphismEmbedding Base q) :
    HasExactCoreAnchoredOriginalPartialCompletions
      n Base Base Core Core (Embedding.id Core) q := by
  intro U _ Test testIn _hCard
  have hTest : Test.IsEHNHomomorphismEmbedding Base
      (q ∘ testIn) :=
    hq.comp testIn.isEHNHomomorphismEmbedding
  have hRoot : HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base (Embedding.id Test) (q ∘ testIn) :=
    HasOriginalPartialTreeExtensionCompletion.root Base
      (q ∘ testIn) hTest.toOriginalPartial
  refine ⟨U, Test, Embedding.id Test, testIn, ?_, ?_, hRoot⟩
  · intro x
    rfl
  · intro z
    constructor
    · intro _
      exact ⟨testIn z, rfl⟩
    · intro _
      exact ⟨z, rfl⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V P VB : Type v}

/-- The ACTUAL relabelled Hales--Jewett power used at the start of
the published functional Picture satisfies the exact closed-core
anchored strict original-partial local completion invariant for
every finite vertex bound n.

The initial strict target tree is the selected full Base copy; the
root map is exactly the old A-part labels followed by A ↪ Base.
Subsequent attachments are handled separately by the conditional
exact-anchor star step. -/
theorem power_relabel_exactCoreAnchoredOriginalPartial
    (A : Structure L U)
    (R : System L U V) (hR : R.WeaklyPartiteOver A)
    (Douter : Structure L P)
    (alpha : Structure.Embedding A Douter)
    (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (N : ℕ) (hN : 0 < N) (n : ℕ) :
    HasExactCoreAnchoredOriginalPartialCompletions
      n Base Base
      (((power R N).relabel alpha.toFunctionEmbedding).toStructure)
      (((power R N).relabel alpha.toFunctionEmbedding).toStructure)
      (Structure.Embedding.id
        (((power R N).relabel alpha.toFunctionEmbedding).toStructure))
      (eAB ∘ (power R N).part) := by
  exact HasExactCoreAnchoredOriginalPartialCompletions.of_core_EHN
    n _ Base (eAB ∘ (power R N).part)
    (power_relabel_originalPartial_EHN_to_base
      A R hR Douter alpha Base eAB N hN)

end StructuralRamsey.FunctionalPartite.Induced

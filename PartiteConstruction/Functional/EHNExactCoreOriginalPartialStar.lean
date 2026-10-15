import PartiteConstruction.Functional.OriginalPartialExactCoreInitialPower
import PartiteConstruction.Functional.EHNAnchoredPictureStar

/-!
# The finite functional Picture with an exact ORIGINAL Hales--Jewett anchor

The printed 2019 Appendix A induction consists of one Hales--Jewett core,
followed by finitely many copies of the old Picture attached over supports
selected inside that ORIGINAL core. The strict original-2019 partial-function
version must keep the canonical labels of the exact tested-core intersection.

All algebraic/geometric lemmas are already available:
* the original core has an exact anchored completion (the EHN projection);
* closed tests pull back to genuine functional free amalgams;
* a relative completion of a tested old core transfers to its exact anchor;
* a copied-side relative extension over the fixed support labels preserves
  the anchored completion after one attachment;
* the original-core-dependent finite star induction retains all old copies.

This module composes these facts. The incoming old-copy relative witness is
an EXPLICIT input for every selected binary attachment test. In particular,
the missing hard multi-generated mixed-root case is NOT asserted or assumed
without being visible in the theorem statement.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P V I VB : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- One actual full-functional stage attachment preserves the exact
original-core rooted B-tree completion invariant, provided the copied
old-stage side has a strict original-2019 partial-function relative
completion over the canonical selected root.

This uses precisely the native `UnitAttachD` free source amalgam; the
original-core map is composed with the distinguished core embedding. -/
theorem Stage.attach_preserves_exactCoreOriginalPartial
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D) (T : Stage K D)
    (core : FunctionalPartite.Embedding E.system T.system)
    (g : FunctionalPartite.Embedding (B.induce S hS) E.system)
    (Base : Structure L VB) (n : ℕ)
    (q : E.Carrier → VB)
    (hOld : HasExactCoreAnchoredOriginalPartialCompletions
      n Base Base E.system.toStructure T.system.toStructure
      core.toEmbedding q)
    (hCopy :
      ∀ (X : Type v) [Finite X]
        (Test : Structure L X)
        (testIn : Structure.Embedding Test
          (Attachment.UnitAttachD B S hS T.system (core.comp g)).toStructure),
        Nat.card X ≤ n →
        let pb :=
          (Attachment.unit_isFreeAmalgam_full
            B S hS T.system (core.comp g)).embeddingPullback testIn
        HasOriginalPartialTreeExtensionCompletion
          (Start := Base) Base pb.toRight
          (q ∘ g.toEmbedding ∘ pb.commonMap)) :
    HasExactCoreAnchoredOriginalPartialCompletions
      n Base Base E.system.toStructure
      (T.attach hK B hB hmB S hS (core.comp g)).system.toStructure
      ((Attachment.coreEmbedding B S hS T.system
        (fun _ : PUnit.{v+1} => core.comp g)).comp core).toEmbedding
      q := by
  have hFactor : ∀ s : S,
      (core.comp g).toEmbedding s = core.toEmbedding (g.toEmbedding s) :=
    fun _ => rfl
  exact
    (Attachment.unit_isFreeAmalgam_full
      B S hS T.system (core.comp g)).hasExactCoreAnchoredOriginalPartialCompletions_attach
      Base Base n core.toEmbedding g.toEmbedding hFactor q hOld hCopy

/-- The published finite star of genuine functional attachments has a
canonical original-core anchored strict original-partial completion.

The only hypothesis beyond the EHN projection of the initial core is
the indicated old-copy relative strict B-tree extension, for every
actual bounded closed test at each intermediate binary attachment.
The finite recursion and all full old-copy embeddings follow from the
already checked `attachAll_preserving_originalCore`, without rerunning
Hales--Jewett or the Ramsey colouring proof. -/
theorem attachAll_exactCoreOriginalPartial
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    [Finite I]
    (Base : Structure L VB) (n : ℕ)
    (q : E.Carrier → VB)
    (hCore : E.system.toStructure.IsEHNHomomorphismEmbedding Base q)
    (hCopy :
      ∀ (T : Stage K D)
        (core : FunctionalPartite.Embedding E.system T.system)
        (g : FunctionalPartite.Embedding (B.induce S hS) E.system),
        HasExactCoreAnchoredOriginalPartialCompletions
          n Base Base E.system.toStructure T.system.toStructure
          core.toEmbedding q →
        ∀ (X : Type v) [Finite X]
          (Test : Structure L X)
          (testIn : Structure.Embedding Test
            (Attachment.UnitAttachD B S hS T.system (core.comp g)).toStructure),
          Nat.card X ≤ n →
          let pb :=
            (Attachment.unit_isFreeAmalgam_full
              B S hS T.system (core.comp g)).embeddingPullback testIn
          HasOriginalPartialTreeExtensionCompletion
            (Start := Base) Base pb.toRight
            (q ∘ g.toEmbedding ∘ pb.commonMap)) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        HasExactCoreAnchoredOriginalPartialCompletions
          n Base Base E.system.toStructure T.system.toStructure
          core.toEmbedding q ∧
        ∀ i, ∃ copy : FunctionalPartite.Embedding B T.system,
          ∀ s : S, copy s.1 = core (maps i s) := by
  let Q : (T : Stage K D) →
      FunctionalPartite.Embedding E.system T.system → Prop :=
    fun T core =>
      HasExactCoreAnchoredOriginalPartialCompletions
        n Base Base E.system.toStructure T.system.toStructure
        core.toEmbedding q
  have hInit : Q E (FunctionalPartite.Embedding.id E.system) :=
    HasExactCoreAnchoredOriginalPartialCompletions.of_core_EHN
      n E.system.toStructure Base q hCore
  have hAttach :
      ∀ (T : Stage K D)
        (core : FunctionalPartite.Embedding E.system T.system)
        (g : FunctionalPartite.Embedding (B.induce S hS) E.system),
        Q T core →
        Q (T.attach hK B hB hmB S hS (core.comp g))
          ((Attachment.coreEmbedding B S hS T.system
            (fun _ : PUnit.{v+1} => core.comp g)).comp core) := by
    intro T core g hQT
    exact Stage.attach_preserves_exactCoreOriginalPartial
      hK B hB hmB S hS E T core g Base n q hQT
      (hCopy T core g hQT)
  exact attachAll_preserving_originalCore
    hK B hB hmB S hS E maps Q hInit hAttach

end StructuralRamsey.FunctionalPartite.EHN

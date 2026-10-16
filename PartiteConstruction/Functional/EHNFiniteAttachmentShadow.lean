import PartiteConstruction.Functional.EHNAttachmentShadowExtensionCriterion
import PartiteConstruction.Functional.EHNStage

/-!
# Simultaneous EHN shadows through a finite list of actual HJ attachments

The genuine native Hales–Jewett Picture first constructs its core power,
then performs a FINITE LIST of full-functional binary attachments of Old
along prescribed full selected-support embeddings. This is not merely
a collection of monochromatic HJ-line embeddings: the index set in
EHN.pictureLemma contains EVERY full partite support embedding.

The one-line parameter-coordinate argument gives a compatible EHN
self-map of the copied old Picture, namely ID. At a CONSTANT-letter
coordinate or a general non-line embedding, an arbitrary corresponding
self-map need not exist (see the adversarial finite graph examples).

This theorem performs the remaining finite gluing bookkeeping in the
natural language of SET-VALUED FUNCTIONS:

Given a control-labelled EHN shadow of the core into Old, and for
EACH prescribed attached full support embedding g_i a control-labelled
EHN endomorphism of Old which agrees with that core shadow on g_i[S],
the whole finite star attachment admits a control-labelled EHN shadow
to Old. Every intermediate picture remains a genuine
FunctionalPartite.System with per-fibre TRANSVERSAL function images.

The proof is a straightforward induction on the ACTUAL attachment
list, and reuses the checked full-functional free-amalgam EHN gluing
criterion. It does not manufacture the copied-side self-maps.
For generic HJ Picture attachments those maps can fail to exist,
even for graphs. This conditional result is an honest interface,
not a proof of the open maximal mixed weak-root theorem.

No generated function-closure of a weak local test is used.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual native FINITE LIST of full-functional partite attachments
retains a global EHN shadow to a fixed old Picture if each attached copy
has a control-labelled EHN self-map of Old agreeing with the core shadow
along that copy's FULL selected-support map.

The entire original core embeds fully, every specified attached copy
has a FULL functional embedding whose support agrees with the corresponding
core placement, and the final EHN shadow's restriction to the original
core is qE. All intermediate
set-valued operation fibres remain part-TRANSVERSAL by construction.

The self-map family is a genuine hypothesis. This theorem is not a
universal HJ Picture retraction and is not a substitute for the open
maximal-mixed strict B-tree relative extension statement. -/
theorem attachList_partCompatibleEHNShadow
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (qE : E.Carrier → V)
    (hqE : E.system.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure qE)
    (hpartE : ∀ x : E.Carrier, B.part (qE x) = E.system.part x)
    (maps : I → FunctionalPartite.Embedding
      (B.induce S hS) E.system)
    (rCopies : I → V → V)
    (hCopies : ∀ i, B.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure (rCopies i))
    (hpartCopies : ∀ i x, B.part (rCopies i x) = B.part x)
    (hAgree : ∀ i (x : S),
      qE (maps i x) = rCopies i x.1)
    (xs : List I) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        ∃ q : T.Carrier → V,
          T.system.toStructure.IsEHNHomomorphismEmbedding
            B.toStructure q ∧
          (∀ x : E.Carrier, q (core x) = qE x) ∧
          (∀ z : T.Carrier, B.part (q z) = T.system.part z) ∧
          (∀ i ∈ xs,
            ∃ copy : FunctionalPartite.Embedding B T.system,
              ∀ x : S, copy x.1 = core (maps i x)) := by
  classical
  induction xs with
  | nil =>
      refine ⟨E, FunctionalPartite.Embedding.id E.system,
        qE, hqE, ?_, hpartE, ?_⟩
      · intro x
        rfl
      · intro i hi
        exact (List.not_mem_nil hi).elim
  | cons i xs ih =>
      obtain ⟨T, core, qT, hqT, hCore, hPartT, hCopiesXs⟩ := ih
      let f : FunctionalPartite.Embedding (B.induce S hS) T.system :=
        core.comp (maps i)
      let R := T.attach hK B hB hmB S hS f
      have hFix : ∀ x : S, qT (f x) = rCopies i x.1 := by
        intro x
        exact (hCore (maps i x)).trans (hAgree i x)
      obtain ⟨qR, hqR, hqCore, _hqCopy, hPartR, _hTrans⟩ :=
        FunctionalPartite.Attachment.unitAttachment_EHN_shadow_partCompatible
          B S hS T.system f
          qT (rCopies i) hqT (hCopies i) hFix hPartT
          (hpartCopies i)
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding B S hS T.system
          (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding B R.system :=
        FunctionalPartite.Attachment.copyEmbedding B S hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, j.comp core, qR, hqR, ?_, hPartR, ?_⟩
      · intro x
        calc
          qR ((j.comp core) x) = qT (core x) := hqCore (core x)
          _ = qE x := hCore x
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · refine ⟨b, ?_⟩
          intro x
          exact FunctionalPartite.Attachment.copy_extends
            B S hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit x
        · obtain ⟨copy, hCopy⟩ := hCopiesXs k hk
          refine ⟨j.comp copy, ?_⟩
          intro x
          exact congrArg j (hCopy x)

end StructuralRamsey.FunctionalPartite.EHN

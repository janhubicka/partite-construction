import PartiteConstruction.Functional.Attachment

/-!
# Track D: sequential FULL native functional attachment without Stage data

A finite list of full selected-support maps into one initial core
can be attached one at a time, preserving a full copy of the
initial core and one full copy of the old source for EACH member
of the original list. Every selected-support vertex agrees exactly
with its designated image in that retained core.

This strips only `K` membership and the EHN part-control certificate
from the already verified EHN.Stage.attachList. The result is a
genuine finite *sequential* functional-partite system, not the
simultaneous indexed free attachment. It preserves part transversality
for genuinely multivalued set-valued functions, uses no global
total-fibre projection, and relies only on full closed-support maps.

Its purpose is to connect the three-line C7 test to the SEQUENTIAL
native attachment geometry used by the actual Ramsey Picture.
A Stage member and its predecessor-rank hypotheses remain separate.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W I : Type v}

/-- Iteration of actual native full functional attachments, carrying
one coherent full embedding of the initial core and one full
embedding of old B for every selected attachment index.

No class-membership, Ramsey-arrow, or strict B-tree target assertion
is hidden in the conclusion. This is the reusable source geometry. -/
theorem attachList_full
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Core : System L P W)
    (maps : I → Embedding (B.induce S hS) Core)
    (xs : List I) :
    ∃ (X : Type v) (T : System L P X),
      ∃ core : Embedding Core T,
        ∀ i ∈ xs, ∃ copy : Embedding B T,
          ∀ x : S, copy x.1 = core (maps i x) := by
  induction xs with
  | nil =>
      exact ⟨W, Core, Embedding.id Core,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons i xs ih =>
      obtain ⟨X, T, core, hcopies⟩ := ih
      let f : Embedding (B.induce S hS) T := core.comp (maps i)
      let New := Attachment.attach
        B S hS T (fun _ : PUnit.{v+1} => f)
      let j : Embedding T New :=
        Attachment.coreEmbedding B S hS T
          (fun _ : PUnit.{v+1} => f)
      let b : Embedding B New :=
        Attachment.copyEmbedding B S hS T
          (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨_, New, j.comp core, ?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨b, ?_⟩
        intro x
        exact Attachment.copy_extends
          B S hS T (fun _ : PUnit.{v+1} => f)
          PUnit.unit x
      · obtain ⟨oldCopy, hOld⟩ := hcopies k hk
        exact ⟨j.comp oldCopy, fun x => congrArg j (hOld x)⟩

end StructuralRamsey.FunctionalPartite

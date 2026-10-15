import PartiteConstruction.Functional.EHNStageInvariant

set_option autoImplicit false

/-!
# Finite Picture stars retaining the ORIGINAL power-core embedding

The published functional Hales--Jewett Picture begins with one power
core E and attaches all old-stage copies along embeddings through E.
For the strict original-2019 partial-function refinement, it is
necessary to remember not only that some intermediate Picture has an
auxiliary property, but WHICH embedding of E into that Picture
determines the canonical root labels.

The existing general-purpose `attachList_preserving` retains a stage
predicate Q but forgets this distinguished embedding.  We prove the
parallel dependent version in which Q is indexed by the embedding of
the original core E.  Each attaching map is exactly `core.comp (maps i)`;
the next distinguished core is exactly `j.comp core` for the new
functional core inclusion j.

This is the finite combinatorial/attachment bookkeeping of the
original published proof.  It makes no additional mathematical
assumption beyond an explicit binary preservation implication.
In particular, if Q expresses strict original-partial anchored local
completion, its binary premise must still construct the relevant
old-copy relative witness for hard multi-generated roots.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Induction over the finite list of actual attached old-stage copies,
retaining the *fixed original* functional Hales--Jewett core embedding.

Unlike a predicate `Q : Stage -> Prop`, the predicate below sees the
distinguished full PARTITE embedding `core : E.system -> T.system`.
The only preservation hypothesis concerns attachment embeddings of the
form `core.comp g`, never arbitrary maps into the enlarged current
stage; that is exactly the construction used in the published Picture.

All copies from previous attachments remain full partite embeddings,
with unchanged canonical labels. -/
theorem attachList_preserving_originalCore
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I)
    (Q : (T : Stage K D) →
      FunctionalPartite.Embedding E.system T.system → Prop)
    (hInit : Q E (FunctionalPartite.Embedding.id E.system))
    (hAttach :
      ∀ (T : Stage K D)
        (core : FunctionalPartite.Embedding E.system T.system)
        (g : FunctionalPartite.Embedding (B.induce S hS) E.system),
        Q T core →
        Q (T.attach hK B hB hmB S hS (core.comp g))
          ((FunctionalPartite.Attachment.coreEmbedding
              B S hS T.system
              (fun _ : PUnit.{v+1} => core.comp g)).comp core)) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        Q T core ∧
        ∀ i ∈ xs, ∃ copy : FunctionalPartite.Embedding B T.system,
          ∀ x : S, copy x.1 = core (maps i x) := by
  induction xs with
  | nil =>
      refine ⟨E, FunctionalPartite.Embedding.id E.system, hInit, ?_⟩
      intro _ h
      exact (List.not_mem_nil h).elim
  | cons i xs ih =>
      obtain ⟨T, core, hQT, hcopies⟩ := ih
      let f := core.comp (maps i)
      let R := T.attach hK B hB hmB S hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding B S hS T.system
          (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding B R.system :=
        FunctionalPartite.Attachment.copyEmbedding B S hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit
      have hQR : Q R (j.comp core) :=
        hAttach T core (maps i) hQT
      refine ⟨R, j.comp core, hQR, ?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨b, ?_⟩
        intro x
        exact FunctionalPartite.Attachment.copy_extends
          B S hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit x
      · obtain ⟨copy, hc⟩ := hcopies k hk
        exact ⟨j.comp copy, fun x => congrArg j (hc x)⟩

/-- Finite index-family form of the same original-core-dependent
Picture invariant, ready to be combined with the existing Hales--Jewett
colouring argument.  The surrounding Ramsey recursion is unchanged. -/
theorem attachAll_preserving_originalCore
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    [Finite I]
    (Q : (T : Stage K D) →
      FunctionalPartite.Embedding E.system T.system → Prop)
    (hInit : Q E (FunctionalPartite.Embedding.id E.system))
    (hAttach :
      ∀ (T : Stage K D)
        (core : FunctionalPartite.Embedding E.system T.system)
        (g : FunctionalPartite.Embedding (B.induce S hS) E.system),
        Q T core →
        Q (T.attach hK B hB hmB S hS (core.comp g))
          ((FunctionalPartite.Attachment.coreEmbedding
              B S hS T.system
              (fun _ : PUnit.{v+1} => core.comp g)).comp core)) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        Q T core ∧
        ∀ i, ∃ copy : FunctionalPartite.Embedding B T.system,
          ∀ x : S, copy x.1 = core (maps i x) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨T, core, hQT, hcopies⟩ :=
    attachList_preserving_originalCore
      hK B hB hmB S hS E maps Finset.univ.toList Q hInit hAttach
  exact ⟨T, core, hQT, fun i => hcopies i (by simp)⟩

end StructuralRamsey.FunctionalPartite.EHN

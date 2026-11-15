import PartiteConstruction.Functional.TrackAActiveOverlapWeakProjection2019
import PartiteConstruction.Functional.EHNStage

/-!
# Track A: exact selected weak-root projections through the ACTUAL EHN attachments

The native EHN Picture step builds a new Stage by attaching finitely
many old-stage copies to a real functional core along FULL closed root
embeddings. It retains a FULL core map and a FULL map for each attached
copy; the part projection itself remains only source-defined/EHN.

The previously verified local active-output-part criterion, together
with its pullback along full part-preserving maps, immediately yields
an invariant on these ACTUAL history maps:

For any selected control-copy support in the NEW attached Stage,
its literal inverse image in the OLD core and in EACH attached copy
admits the correct original-2019 source-defined weak projection.
These are the exact weak carriers used by the source-side Picture
decomposition; no closure hull, domain reflection or artificial
re-embedding is inserted.

This theorem retains the precise attachment map equations on every
closed root, and uses the actual Stage.attachList witness, rather than
an abstract free-amalgam substitute. It does NOT assert that the
resulting source maps can be promoted to full functional embeddings,
nor does it provide a common strict target B-tree for all mixed tests.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V I Q : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- An ACTUAL finite native EHN star attachment carries the
original-partial weak projection on all selected-support pullbacks:
both the old core and each attached copy, on their literal vertex
preimages, with the exact part-image target.

The original attachment equations along the closed common roots are
preserved simultaneously. This is only a source-side root invariant;
no strict functional target-tree witness is constructed. -/
theorem attachList_selectedSupport_preimage_originalPartial
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D)
    (hmB : K B.toStructure)
    (Root : Set V) (hRoot : B.toStructure.IsClosed Root)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce Root hRoot) E.system)
    (indices : List I)
    (α : Q ↪ P) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        Structure.IsOriginalPartialHomomorphism
          (E.system.toStructure.weakInduce
            (core.toFun ⁻¹' T.system.support α))
          (D.weakInduce
            (E.system.part '' (core.toFun ⁻¹' T.system.support α)))
          (clippedWeakImageMap E.system.part
            (core.toFun ⁻¹' T.system.support α)) ∧
        ∀ i ∈ indices,
          ∃ copy : FunctionalPartite.Embedding B T.system,
            (∀ x : Root, copy x.1 = core (maps i x)) ∧
            (∀ x : Root,
              x.1 ∈ copy.toFun ⁻¹' T.system.support α ↔
                maps i x ∈ core.toFun ⁻¹' T.system.support α) ∧
            Structure.IsOriginalPartialHomomorphism
              (B.toStructure.weakInduce
                (copy.toFun ⁻¹' T.system.support α))
              (D.weakInduce
                (B.part '' (copy.toFun ⁻¹' T.system.support α)))
              (clippedWeakImageMap B.part
                (copy.toFun ⁻¹' T.system.support α)) := by
  obtain ⟨T, core, hcopies⟩ :=
    attachList hK B hB hmB Root hRoot E maps indices
  let Cut : Set T.Carrier := T.system.support α
  have hCut : T.system.ActiveWeakOutputPartCover Cut :=
    T.system.support_activeWeakOutputPartCover α
  refine ⟨T, core, ?_, ?_⟩
  · exact core.preimage_originalPartialWeakProjection
      D E.isPartite Cut hCut
  · intro i hi
    obtain ⟨copy, hext⟩ := hcopies i hi
    refine ⟨copy, hext, ?_, ?_⟩
    · intro x
      change copy.toFun x.1 ∈ Cut ↔ core.toFun (maps i x) ∈ Cut
      rw [hext x]
    · exact copy.preimage_originalPartialWeakProjection
        D hB Cut hCut

end StructuralRamsey.FunctionalPartite.EHN

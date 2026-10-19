import PartiteConstruction.Functional.OutputPartSplitFreeAmalgam
import PartiteConstruction.Functional.EHNStage

/-!
# The ACTUAL native finite HJ attachment retains ALL split full source copies

The verified native EHN Stage.attachList constructs a genuine
finite FULL functional partite stage by iterating full free
attachments over an actual closed support S. It retains one
FULL core embedding and each prescribed FULL old-copy embedding.

The canonical per-output-part singleton translation of these
full partite maps has exactly the same underlying vertex map
and therefore exactly the same support-overlap equations.
This is a direct statement about the real functional Picture,
not a separately constructed relational/U-closed surrogate.

No global HJ coordinate retraction is assumed, even if the
attached lines have disjoint parameter-coordinate sets.
No arbitrary weak S is treated as a full gluing root, and
no compatible strict TARGET B-tree profile is fabricated.

When arbitrary exact weak vertex sets are tested afterward,
the checked split-output-part weak free-amalgam theorem
supplies the corresponding literal source root/side geometry.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Actual native finite full-functional attachment list:
after output-part singletonization, its final SAME native
stage has a FULL core map and a FULL copy map for each
listed old-stage index, with the ORIGINAL exact closed
support overlap equation.

No copy, stage, tested weak vertex set, or output-fibre
incidence is replaced by a new relational construction. -/
theorem attachList_splitCopies
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding
        E.system.splitOutputParts T.system.splitOutputParts,
        ∀ i ∈ xs,
          ∃ copy : FunctionalPartite.Embedding
            B.splitOutputParts T.system.splitOutputParts,
            ∀ x : S,
              copy x.1 =
                core ((maps i).splitOutputParts x) := by
  obtain ⟨T, core, hCopies⟩ :=
    attachList hK B hB hmB S hS E maps xs
  refine ⟨T, core.splitOutputParts, ?_⟩
  intro i hi
  obtain ⟨copy, hCopy⟩ := hCopies i hi
  refine ⟨copy.splitOutputParts, ?_⟩
  intro x
  exact hCopy x

/-- The same source-side correspondence for EVERY member
of any FINITE actual functional HJ line attachment family.
No common parameter coordinate or global old-stage
retraction is asserted. -/
theorem attachAll_splitCopies
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D) [Finite I]
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding
        E.system.splitOutputParts T.system.splitOutputParts,
        ∀ i : I,
          ∃ copy : FunctionalPartite.Embedding
            B.splitOutputParts T.system.splitOutputParts,
            ∀ x : S,
              copy x.1 =
                core ((maps i).splitOutputParts x) := by
  obtain ⟨T, core, hCopies⟩ :=
    attachAll hK B hB hmB S hS E maps
  refine ⟨T, core.splitOutputParts, ?_⟩
  intro i
  obtain ⟨copy, hCopy⟩ := hCopies i
  refine ⟨copy.splitOutputParts, ?_⟩
  intro x
  exact hCopy x

end StructuralRamsey.FunctionalPartite.EHN

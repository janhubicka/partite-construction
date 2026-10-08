import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.EHNAttachmentGraphIso

/-! # Native EHN attachment stages and their weak-test graph geometry

The direct functional EHN iteration attaches one *genuine function
structure* to another along a closed support.  Its full free amalgam
has the same function graph as the ordinary relational free attachment.
This correspondence is only used to analyze arbitrary weak vertex tests.

No U-closed graph-stage construction or recursive function-repair pass
is introduced here.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual one-copy EHN attachment used in the Picture construction
is the graph of a full set-valued-function free attachment. -/
noncomputable def Stage.attachGraphIso
    (T : Stage K D)
    (hK : Structure.FreeAmalgamationClass K)
    (B : FunctionalPartite.System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (f : FunctionalPartite.Embedding (B.induce S hS) T.system) :
    RelStructure.Iso
      ((T.attach hK B hB hmB S hS f).system.toStructure.graph)
      (RelStructure.Attachment.attach B.toStructure.graph S
        T.system.toStructure.graph
        (fun _ : PUnit.{v+1} =>
          Structure.Attachment.attachingGraphMap B.toStructure S hS
            T.system.toStructure f.toEmbedding)) := by
  exact Structure.Attachment.graphAttachmentIso
    B.toStructure S hS T.system.toStructure
    (fun _ : PUnit.{v+1} => f.toEmbedding)

end StructuralRamsey.FunctionalPartite.EHN

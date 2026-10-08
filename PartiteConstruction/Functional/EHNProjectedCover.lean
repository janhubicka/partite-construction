import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.EHNPictureInvariant
import PartiteConstruction.Functional.EHNInvariantConstruction

/-! # The published projected-coverage invariant for genuine functions

Every irreducible of a picture projects into a B-copy in the original
witness. The core and attachment lemmas below use the actual native
Hales--Jewett power and full closed supports. The initial picture and full
pass, with arbitrary function arities, are in EHNProjectedCoverAllArity.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure
universe u v
variable {L : Language.{u}} {U V W P : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- Intermediate projected coverage, not final extension inside the picture. -/
def Stage.ProjectedCover (Base : Structure L V) (T : Stage K D) : Prop :=
  Structure.ProjectsIrreduciblesInto Base T.system.toStructure D T.system.part

/-- Binary native attachments preserve projected irreducible coverage. -/
theorem Stage.attach_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) (T : Stage K D)
    (B : System L P W) [Finite W]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set W) (hS : B.toStructure.IsClosed S)
    (f : FunctionalPartite.Embedding (B.induce S hS) T.system)
    (hT : T.ProjectedCover Base)
    (hCovB : Structure.ProjectsIrreduciblesInto Base B.toStructure D B.part) :
    (T.attach hK B hB hmB S hS f).ProjectedCover Base := by
  apply Structure.ProjectsIrreduciblesInto.of_freeAmalgam
    (Structure.Attachment.unit_isFreeAmalgam
      B.toStructure S hS T.system.toStructure f.toEmbedding) hT hCovB
  · intro x
    rfl
  · intro x
    exact FunctionalPartite.Attachment.part_copyMap
      B S hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit x

/-- One weak coordinate localizes every full irreducible of the exact
power core to an irreducible hull in the old picture. -/
theorem pictureLemma_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (Base : Structure L V) (B : Stage K D)
    (hB : B.ProjectedCover Base) (alpha : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D,
      C.ProjectedCover Base ∧ PictureProperty A B C alpha κ := by
  apply pictureLemma_preserving hK A hA B alpha κ
    (fun T => T.ProjectedCover Base)
  · intro N hN
    let R := B.system.weakRestrict D B.isPartite.1 A alpha
    let S := B.system.support alpha.toFunctionEmbedding
    have hS : B.system.toStructure.IsClosed S :=
      B.system.weak_support_closed D B.isPartite.1 A alpha
    let inc : Structure.Embedding R.toStructure B.system.toStructure :=
      Structure.inclusion B.system.toStructure S hS
    have hR : Structure.ProjectsIrreduciblesInto Base R.toStructure D
        (B.system.part ∘ inc) := hB.precomp_weak inc.isWeakHomomorphism
    let i0 : Fin N := ⟨0, hN⟩
    have hPower : Structure.ProjectsIrreduciblesInto Base
        (Induced.power R N).toStructure D
        ((B.system.part ∘ inc) ∘ (fun z => z.coord i0)) :=
      hR.precomp_weak (Induced.coordinateWeak (B := R) i0)
    change Structure.ProjectsIrreduciblesInto Base
      (Induced.power R N).toStructure D (fun z => alpha z.part)
    apply hPower.congr
    intro z
    exact (congrArg alpha (z.belongs i0)).symm.trans
      (B.system.restrictedPart_spec alpha.toFunctionEmbedding (z.coord i0))
  · intro T S hS f hT
    exact T.attach_projectedCover hK Base B.system B.isPartite B.mem S hS f hT hB

end StructuralRamsey.FunctionalPartite.EHN

import PartiteConstruction.Functional.EHNLineOnlyConstruction
import PartiteConstruction.Functional.EHNProjectedCoverAllArity

/-!
# Genuine functional HJ LINE-only Picture preserves projected B-cover

The verified original native EHN Picture carries two independent
facts: the Ramsey PictureProperty, and coverage of every FULL
irreducible of a functional stage by the projection of some FULL
B-copy in the original control D.

The narrowed Hales-Jewett LINE-indexed Picture needs exactly these
same facts. The POWER core has projected coverage because one
coordinate weakly projects its irreducible shadows to an old
function-closed irreducible hull; every attached OLD copy preserves
projected coverage across the genuine full free functional amalgam.
The line-only Picture lemma makes no additional geometric demand:
it iterates those SAME attachments, simply over a smaller finite
family of full support embeddings.

Combining this with the already verified rooted initial Picture and
abstract finite canonicalization gives a complete class-preserving
induced functional Ramsey pass (arbitrary function arities), using
only HJ-line attachments, while still preserving the published
projected irreducible B-coverage invariant at every stage.

All function outputs are genuine set-valued and PART-TRANSVERSAL.
This result does NOT yet assert strict full-functional B-tree
completions of arbitrary mixed exact WEAK tests across many lines.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- One genuine functional line-indexed Hales-Jewett Picture step,
retaining both the Ramsey PictureProperty and projected irreducible
B-coverage. No arbitrary support embeddings beyond actual lines
are attached. -/
theorem pictureLemma_lines_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (Base : Structure L V)
    (Old : Stage K D) (hOld : Old.ProjectedCover Base)
    (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D,
      C.ProjectedCover Base ∧ PictureProperty A Old C α κ := by
  apply pictureLemma_lines_preservingSupport
    hK A hA Old α κ
    (fun T => T.ProjectedCover Base)
  · intro N hN
    let R := Old.system.weakRestrict D Old.isPartite.1 A α
    let S := Old.system.support α.toFunctionEmbedding
    have hS : Old.system.toStructure.IsClosed S :=
      Old.system.weak_support_closed D Old.isPartite.1 A α
    let inc : Structure.Embedding
        R.toStructure Old.system.toStructure :=
      Structure.inclusion Old.system.toStructure S hS
    have hR : Structure.ProjectsIrreduciblesInto Base
        R.toStructure D (Old.system.part ∘ inc) :=
      hOld.precomp_weak inc.isWeakHomomorphism
    let i0 : Fin N := ⟨0, hN⟩
    have hPower : Structure.ProjectsIrreduciblesInto Base
        (Induced.power R N).toStructure D
        ((Old.system.part ∘ inc) ∘ (fun z => z.coord i0)) :=
      hR.precomp_weak (Induced.coordinateWeak (B := R) i0)
    change Structure.ProjectsIrreduciblesInto Base
      (Induced.power R N).toStructure D (fun z => α z.part)
    apply hPower.congr
    intro z
    exact (congrArg α (z.belongs i0)).symm.trans
      (Old.system.restrictedPart_spec
        α.toFunctionEmbedding (z.coord i0))
  · intro T f hT
    exact T.attach_projectedCover hK Base
      Old.system Old.isPartite Old.mem
      (Old.system.support α.toFunctionEmbedding)
      (Old.system.weak_support_closed D Old.isPartite.1 A α)
      f hT hOld

/-- Complete genuine functional induced Ramsey pass through HJ
LINE-only attachments, also preserving the FULL projected
irreducible B-coverage invariant. Includes nullary functions via
the verified rooted initial Picture. -/
theorem inducedConstruction_allArity_lines_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U)
    (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hBase : K Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ) :
    ∃ T : Stage K D,
      T.ProjectedCover Base ∧
      Structure.Arrow A Base T.system.toStructure κ := by
  classical
  apply inducedConstruction_preserving A Base D κ hRamsey
    (fun T => T.ProjectedCover Base)
  · intro beta0
    letI : Fintype (Structure.Embedding Base D) :=
      Fintype.ofFinite _
    obtain ⟨T, hT, _root, _hroot, hcopies⟩ :=
      initialList_allArity_projectedCover
        hK Base hBase beta0 Finset.univ.toList
    exact ⟨T, hT, fun beta => hcopies beta (by simp)⟩
  · intro T alpha hT
    exact pictureLemma_lines_projectedCover
      hK A hA Base T hT alpha κ

end StructuralRamsey.FunctionalPartite.EHN

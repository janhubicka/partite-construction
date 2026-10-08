import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.EHNPictureInvariant
import PartiteConstruction.Functional.EHNInvariantConstruction

/-! # The published projected-coverage invariant for genuine functions

The original induced construction promises that every irreducible of a
picture projects into a B-copy in the original witness. We retain that
assertion with the correct EHN weak projection, using the actual native
Hales--Jewett power and full closed-support free attachments.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure
universe u v
variable {L : Language.{u}} {U V W P : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- The intermediate projected-copy invariant, not yet final extension
inside the current picture. -/
def Stage.ProjectedCover (Base : Structure L V) (T : Stage K D) : Prop :=
  Structure.ProjectsIrreduciblesInto Base T.system.toStructure D T.system.part

/-- A binary native attachment preserves projected irreducible coverage. -/
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

/-- Projected coverage of the exact coordinatewise core follows by taking
one weak coordinate and localizing its irreducible image in the old picture. -/
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
    have hPower := hR.precomp_weak (Induced.coordinateWeak (B := R) i0)
    change Structure.ProjectsIrreduciblesInto Base
      (Induced.power R N).toStructure D (fun z => alpha z.part)
    apply hPower.congr
    intro z
    exact (congrArg alpha (z.belongs i0)).symm.trans
      (B.system.restrictedPart_spec alpha.toFunctionEmbedding (z.coord i0))
  · intro T S hS f hT
    exact T.attach_projectedCover hK Base B.system B.isPartite B.mem S hS f hT hB

/-- The disjoint initial picture, carrying the actual projected B-copies. -/
theorem initialList_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V]
    (hBase : K Base) (hpos : L.PositiveFuncArity)
    (beta0 : Structure.Embedding Base D)
    (xs : List (Structure.Embedding Base D)) :
    ∃ T : Stage K D, T.ProjectedCover Base ∧
      ∃ root : Structure.Embedding Base T.system.toStructure,
        ∀ beta ∈ xs, ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  induction xs with
  | nil =>
    let T : Stage K D := {
      Carrier := V
      finiteCarrier := inferInstance
      system := placed Base beta0
      isPartite := placed_over Base beta0
      mem := hBase
    }
    exact ⟨T, Structure.ProjectsIrreduciblesInto.base beta0,
      Structure.Embedding.id Base, fun _ h => (List.not_mem_nil h).elim⟩
  | cons beta xs ih =>
    obtain ⟨T, hT, root, hcopies⟩ := ih
    let B := placed Base beta
    have hS : B.toStructure.IsClosed ∅ := empty_closed Base hpos
    let f : FunctionalPartite.Embedding (B.induce ∅ hS) T.system := {
      toEmbedding := root.comp (Structure.inclusion Base ∅ hS)
      map_part := fun x => x.2.elim
    }
    let R := T.attach hK B (placed_over Base beta) hBase ∅ hS f
    have hR : R.ProjectedCover Base :=
      T.attach_projectedCover hK Base B (placed_over Base beta) hBase
        ∅ hS f hT (Structure.ProjectsIrreduciblesInto.base beta)
    let j : FunctionalPartite.Embedding T.system R.system :=
      FunctionalPartite.Attachment.coreEmbedding
        B ∅ hS T.system (fun _ : PUnit.{v+1} => f)
    let b : FunctionalPartite.Embedding B R.system :=
      FunctionalPartite.Attachment.copyEmbedding
        B ∅ hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
    refine ⟨R, hR, j.toEmbedding.comp root, ?_⟩
    intro gamma hgamma
    rcases List.mem_cons.mp hgamma with rfl | hgamma
    · exact ⟨b.toEmbedding, b.map_part⟩
    · obtain ⟨e, he⟩ := hcopies gamma hgamma
      exact ⟨j.toEmbedding.comp e, fun x => (j.map_part (e x)).trans (he x)⟩

/-- One genuine-function induced pass, retaining the projected-coverage
conclusion required by the published final-extension argument. -/
theorem inducedConstruction_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hBase : K Base) (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ) :
    ∃ T : Stage K D,
      T.ProjectedCover Base ∧ Structure.Arrow A Base T.system.toStructure κ := by
  classical
  apply inducedConstruction_preserving A Base D κ hArrow
    (fun T => T.ProjectedCover Base)
  · intro beta0
    letI : Fintype (Structure.Embedding Base D) := Fintype.ofFinite _
    obtain ⟨T, hT, _root, hcopies⟩ :=
      initialList_projectedCover hK Base hBase hpos beta0 Finset.univ.toList
    exact ⟨T, hT, fun beta => hcopies beta (by simp)⟩
  · intro T alpha hT
    exact pictureLemma_projectedCover hK A hA Base T hT alpha κ

end StructuralRamsey.FunctionalPartite.EHN

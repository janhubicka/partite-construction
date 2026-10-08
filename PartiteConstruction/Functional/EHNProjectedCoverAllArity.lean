import PartiteConstruction.Functional.EHNProjectedCover

/-! # Projected coverage with arbitrary function arities

When constants are present the initial copies share their canonical closed
nullary root instead of being disjoint. The existing root transport aligns
all placements in D. Projected coverage then survives exactly the same full
free attachments and Picture steps; no change to the Ramsey proof is needed.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure
universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- Initial B-copies with their common nullary root and projected coverage. -/
theorem initialList_allArity_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V] (hBase : K Base)
    (beta0 : Structure.Embedding Base D)
    (xs : List (Structure.Embedding Base D)) :
    ∃ T : Stage K D, T.ProjectedCover Base ∧
      ∃ root : Structure.Embedding Base T.system.toStructure,
        (∀ x, T.system.part (root x) = beta0 x) ∧
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
      Structure.Embedding.id Base, (fun _ => rfl),
      fun _ h => (List.not_mem_nil h).elim⟩
  | cons beta xs ih =>
    obtain ⟨T, hT, root, hroot, hcopies⟩ := ih
    let B := placed Base beta
    let S : Set V := Base.nullaryRoot
    have hS : B.toStructure.IsClosed S := Base.nullaryRoot_isClosed
    let phi := rootTransport Base beta0 beta
    let incRoot : Structure.Embedding
        (Base.induce Base.nullaryRoot Base.nullaryRoot_isClosed) Base :=
      Structure.inclusion Base Base.nullaryRoot Base.nullaryRoot_isClosed
    let f : FunctionalPartite.Embedding (B.induce S hS) T.system := {
      toEmbedding := root.comp (incRoot.comp phi)
      map_part := by
        intro x
        exact (hroot (incRoot (phi x))).trans (rootTransport_spec Base beta0 beta x)
    }
    let R := T.attach hK B (placed_over Base beta) hBase S hS f
    have hR : R.ProjectedCover Base :=
      T.attach_projectedCover hK Base B (placed_over Base beta) hBase
        S hS f hT (Structure.ProjectsIrreduciblesInto.base beta)
    let j : FunctionalPartite.Embedding T.system R.system :=
      FunctionalPartite.Attachment.coreEmbedding
        B S hS T.system (fun _ : PUnit.{v+1} => f)
    let b : FunctionalPartite.Embedding B R.system :=
      FunctionalPartite.Attachment.copyEmbedding
        B S hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
    refine ⟨R, hR, j.toEmbedding.comp root, ?_, ?_⟩
    · intro x
      exact (j.map_part (root x)).trans (hroot x)
    · intro gamma hgamma
      rcases List.mem_cons.mp hgamma with rfl | hgamma
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hcopies gamma hgamma
        exact ⟨j.toEmbedding.comp e, fun x => (j.map_part (e x)).trans (he x)⟩

/-- A full native Ramsey pass retaining projected irreducible B-coverage,
with no restriction on function arities, including nullary functions. -/
theorem inducedConstruction_allArity_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hBase : K Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ) :
    ∃ T : Stage K D,
      T.ProjectedCover Base ∧ Structure.Arrow A Base T.system.toStructure κ := by
  classical
  apply inducedConstruction_preserving A Base D κ hArrow
    (fun T => T.ProjectedCover Base)
  · intro beta0
    letI : Fintype (Structure.Embedding Base D) := Fintype.ofFinite _
    obtain ⟨T, hT, _root, _hroot, hcopies⟩ :=
      initialList_allArity_projectedCover hK Base hBase beta0 Finset.univ.toList
    exact ⟨T, hT, fun beta => hcopies beta (by simp)⟩
  · intro T alpha hT
    exact pictureLemma_projectedCover hK A hA Base T hT alpha κ

end StructuralRamsey.FunctionalPartite.EHN

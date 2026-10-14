import PartiteConstruction.Functional.EHNCombinedPictureWeakTreeCover
import PartiteConstruction.Functional.EHNInitialWeakTree

/-!
# Published initial picture: both weak-tree and projected B-cover

The initial functional picture is the same disjoint family of full B-copies
as in the published proof (positive function arities). Each full attachment
preserves both the n-vertex induced function-GRAPH tree invariant and projected
B-copy coverage. The witnesses remain on the same genuine functional stage.
No Ramsey recursion or U-closed relational intermediate objects are used.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The original initial Picture carries local weak function-graph tree
witnesses and the projected irreducible B-copy covering simultaneously. -/
theorem initialList_weakTree_and_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U]
    (Base : Structure L V) [Finite V] [Finite P]
    (hBase : K Base)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding Base D)
    (xs : List (Structure.Embedding Base D))
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph Base.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph Base.graph
        T.system.toStructure.graph n ∧
      T.ProjectedCover Base ∧
      ∃ root : Structure.Embedding Base T.system.toStructure,
        ∀ β ∈ xs,
          ∃ j : Structure.Embedding Base T.system.toStructure,
            ∀ x, T.system.part (j x) = β x := by
  classical
  induction xs with
  | nil =>
      let T : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed Base β₀
        isPartite := placed_over Base β₀
        mem := hBase
      }
      refine ⟨T, ?_, ?_, Structure.Embedding.id Base, ?_⟩
      · exact base_weakGraphLocallyTreeLike A Base n
      · exact Structure.ProjectsIrreduciblesInto.base β₀
      · intro _ h
        exact (List.not_mem_nil h).elim
  | cons β xs ih =>
      obtain ⟨T, hTTree, hTCov, root, hcopies⟩ := ih
      let B := placed Base β
      have hS : B.toStructure.IsClosed ∅ := empty_closed Base hpos
      let f : FunctionalPartite.Embedding (B.induce ∅ hS) T.system := {
        toEmbedding := root.comp (Structure.inclusion Base ∅ hS)
        map_part := fun x => x.2.elim
      }
      let BStage : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := B
        isPartite := placed_over Base β
        mem := hBase
      }
      let R := T.attach hK B (placed_over Base β) hBase ∅ hS f
      have hSupport : ∀ x : V, x ∈ (∅ : Set V) →
          ∃ a : U, B.part x = (β₀.comp eAB) a := by
        intro x hx
        exact hx.elim
      have hBCov : BStage.ProjectedCover Base :=
        Structure.ProjectsIrreduciblesInto.base β
      have hR :
          RelStructure.LocallyTreeLike A.graph Base.graph
            R.system.toStructure.graph n ∧
          R.ProjectedCover Base := by
        exact Stage.attach_weakTree_and_projectedCover
          hK A Base D hA eAB BStage T ∅ hS f
          (β₀.comp eAB) hSupport n hn hD
          (base_weakGraphLocallyTreeLike A Base n) hTTree
          hBCov hTCov
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding
          B ∅ hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding B R.system :=
        FunctionalPartite.Attachment.copyEmbedding
          B ∅ hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, hR.1, hR.2, j.toEmbedding.comp root, ?_⟩
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hcopies γ hγ
        exact ⟨j.toEmbedding.comp e,
          fun x => (j.map_part (e x)).trans (he x)⟩

/-- One finite native initial Picture simultaneously represents every
B-placement in D, controls weak test size, and preserves projected B-cover. -/
theorem initial_weakTree_and_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U]
    (Base : Structure L V) [Finite V] [Finite P]
    (hBase : K Base)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding Base D)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph Base.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph Base.graph
        T.system.toStructure.graph n ∧
      T.ProjectedCover Base ∧
      ∀ β : Structure.Embedding Base D,
        ∃ j : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (j x) = β x := by
  classical
  letI : Fintype (Structure.Embedding Base D) := Fintype.ofFinite _
  obtain ⟨T, hTree, hCover, _, hCopies⟩ :=
    initialList_weakTree_and_projectedCover
      hK A Base hBase hA eAB hpos β₀ Finset.univ.toList n hn hD
  exact ⟨T, hTree, hCover, fun β => hCopies β (by simp)⟩

end

end StructuralRamsey.FunctionalPartite.EHN

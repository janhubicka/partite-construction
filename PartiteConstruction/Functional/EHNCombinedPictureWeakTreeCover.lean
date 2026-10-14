import PartiteConstruction.Functional.EHNCombinedWeakTreeCover
import PartiteConstruction.Functional.EHNPictureWeakTree
import PartiteConstruction.Functional.EHNProjectedCover

/-!
# Published Picture induction: weak vertex trees AND projected B-cover

One genuine functional Picture step preserves both invariants simultaneously
on the very same output. This is the two-case induction of the published
Appendix A with the necessary correction to weak vertex tests.

Weak tests retain precisely the chosen vertices; function outputs leaving
the test become undefined there. The local tree target is a RELATIONAL
function-graph B-tree, not an asserted full-functional strict B-tree.

The proof shares the original power core and every native free attachment.
It does not re-run the recursive construction or introduce U-closed
relational Picture stages.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The original 2019 Picture step carries local weak function-graph
tree control AND irreducible-to-B projected coverage together. -/
theorem pictureLemma_weakTree_and_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] [Finite P] (hKA : K A)
    (Base : Structure L V) [Finite V]
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (Old : Stage K D)
    (hOldCover : Old.ProjectedCover Base)
    (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ]
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph Base.graph D.graph (n - 1))
    (hOldTree : RelStructure.LocallyTreeLike A.graph Base.graph
      Old.system.toStructure.graph n) :
    ∃ C : Stage K D,
      RelStructure.LocallyTreeLike A.graph Base.graph
        C.system.toStructure.graph n ∧
      C.ProjectedCover Base ∧
      PictureProperty A Old C α κ := by
  classical
  let Q : Stage K D → Prop := fun C =>
    RelStructure.LocallyTreeLike A.graph Base.graph
      C.system.toStructure.graph n ∧
    C.ProjectedCover Base
  have hCore :
      ∀ (N : ℕ) (hN : 0 < N),
        let R := Old.system.weakRestrict D Old.isPartite.1 A α
        let hR : R.WeaklyPartiteOver A :=
          Old.system.weakRestrict_invariant
            D Old.isPartite.1 A α Old.isPartite
        let E := Induced.power R N
        let hPower : E.WeaklyPartiteOver A :=
          Induced.power_weaklyPartiteOver hR hN
        let ER := E.relabel α.toFunctionEmbedding
        let hER : ER.WeaklyPartiteOver D :=
          α.isEHNHomomorphismEmbedding.comp hPower
        let T : Stage K D := {
          Carrier := Induced.Vertex R N
          finiteCarrier := inferInstance
          system := ER
          isPartite := hER
          mem := mem_of_weaklyPartiteOver hK E hPower hKA
        }
        Q T := by
    intro N hN
    let R := Old.system.weakRestrict D Old.isPartite.1 A α
    have hR : R.WeaklyPartiteOver A :=
      Old.system.weakRestrict_invariant
        D Old.isPartite.1 A α Old.isPartite
    let E := Induced.power R N
    have hPower : E.WeaklyPartiteOver A :=
      Induced.power_weaklyPartiteOver hR hN
    have hProj : E.toStructure.graph.IsHomomorphismEmbedding A.graph E.part :=
      hPower.graphHomomorphismEmbedding
    have hLTL :
        RelStructure.LocallyTreeLike A.graph Base.graph
          E.toStructure.graph n :=
      RelStructure.LocallyTreeLike.of_homEmbedding_to_base
        hA.irreducible eAB.graph E.part hProj n
    let S := Old.system.support α.toFunctionEmbedding
    have hS : Old.system.toStructure.IsClosed S :=
      Old.system.weak_support_closed D Old.isPartite.1 A α
    let inc : Structure.Embedding R.toStructure Old.system.toStructure :=
      Structure.inclusion Old.system.toStructure S hS
    have hRootCov : Structure.ProjectsIrreduciblesInto Base R.toStructure D
        (Old.system.part ∘ inc) :=
      hOldCover.precomp_weak inc.isWeakHomomorphism
    let i0 : Fin N := ⟨0, hN⟩
    have hPowerCov : Structure.ProjectsIrreduciblesInto Base
        E.toStructure D
        ((Old.system.part ∘ inc) ∘ (fun z => z.coord i0)) :=
      hRootCov.precomp_weak (Induced.coordinateWeak (B := R) i0)
    have hCover : Structure.ProjectsIrreduciblesInto Base
        E.toStructure D (fun z => α.toFunctionEmbedding z.part) := by
      apply hPowerCov.congr
      intro z
      exact (congrArg α (z.belongs i0)).symm.trans
        (Old.system.restrictedPart_spec α.toFunctionEmbedding (z.coord i0))
    constructor
    · exact hLTL
    · exact hCover
  have hAttach :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support α.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A α))
          T.system),
        Q T →
        Q (T.attach hK Old.system Old.isPartite Old.mem
          (Old.system.support α.toFunctionEmbedding)
          (Old.system.weak_support_closed D Old.isPartite.1 A α) f) := by
    intro T f hT
    let S := Old.system.support α.toFunctionEmbedding
    have hS : Old.system.toStructure.IsClosed S :=
      Old.system.weak_support_closed D Old.isPartite.1 A α
    have hSupport : ∀ x : Old.Carrier, x ∈ S →
        ∃ a : U, Old.system.part x = α a := by
      intro x hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, ha.symm⟩
    exact Stage.attach_weakTree_and_projectedCover
      hK A Base D hA eAB Old T S hS f α hSupport
      n hn hD hOldTree hT.1 hOldCover hT.2
  obtain ⟨C, hC, hPicture⟩ :=
    pictureLemma_preservingSupport hK A hKA Old α κ Q hCore hAttach
  exact ⟨C, hC.1, hC.2, hPicture⟩

end

end StructuralRamsey.FunctionalPartite.EHN

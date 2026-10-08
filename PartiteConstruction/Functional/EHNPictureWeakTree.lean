import PartiteConstruction.Functional.EHNWeakAttachmentStep
import PartiteConstruction.Functional.EHNPictureInvariant
import PartiteConstruction.Functional.WeakInvariant

/-! # The actual functional EHN Picture preserves weak vertex-tree ranks

The Hales--Jewett core is an actual set-valued-function power.  Its
global EHN projection, although only weak on arbitrary function outputs,
becomes a graph homomorphism-embedding on weak tests.  It therefore has
the controlled one-copy tree bound at every vertex rank.

Each old-copy attachment is a genuine full functional free attachment
over precisely the *closed support* of the chosen A-placement.  Applying
the generic projected weak-graph attachment lemma to that native stage
preserves the rank n.  The already checked EHN Picture colouring and
finite attachment bookkeeping then give the result without U-closed
relational Picture stages.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- One actual EHN Hales--Jewett Picture step preserves controlled
weak graph-tree local completability at n vertices while retaining
full function-language Picture canonicalization and class membership. -/
theorem pictureLemma_weakGraphLocallyTreeLike
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] [Finite P] (hKA : K A)
    (Base : Structure L V) [Finite V]
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (Old : Stage K D)
    (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ]
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph Base.graph D.graph (n - 1))
    (hOld : RelStructure.LocallyTreeLike A.graph Base.graph
      Old.system.toStructure.graph n) :
    ∃ C : Stage K D,
      RelStructure.LocallyTreeLike A.graph Base.graph
        C.system.toStructure.graph n ∧
      PictureProperty A Old C α κ := by
  classical
  let Q : Stage K D → Prop := fun C =>
    RelStructure.LocallyTreeLike A.graph Base.graph
      C.system.toStructure.graph n
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
    simpa [Q, FunctionalPartite.System.relabel] using hLTL
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
    exact Stage.attach_weakGraphLocallyTreeLike hK A Base D
      hA eAB Old T S hS f α hSupport n hn hD hOld hT
  exact pictureLemma_preservingSupport hK A hKA Old α κ Q hCore hAttach

end

end StructuralRamsey.FunctionalPartite.EHN

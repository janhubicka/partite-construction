import PartiteConstruction.Iterated.GenericProjectedAttachmentStep
import PartiteConstruction.Iterated.IsoTransport
import PartiteConstruction.Functional.EHNStageAttachmentGraph
import PartiteConstruction.Functional.EHNProjectionGraphBridge

/-! # Weak vertex-size tree induction through a genuine functional attachment

The native EHN Picture attaches copies of actual set-valued-function
structures along a genuinely function-closed support.  Passing to function
graphs is only an interpretation of arbitrary weak vertex tests.  The
generic projected relational attachment lemma applies via the canonical
graph isomorphism of the *actual* full functional free attachment.

Neither this statement nor its proof constructs a U-closed relational
Picture. The full functional embeddings are inherited from the native
EHN attachment construction.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}

/-- A single full functional EHN attachment preserves controlled weak
function-graph local tree completability at rank n. Only the *selected*
function-closed overlap is required to project into the specified A-copy. -/
theorem Stage.attach_weakGraphLocallyTreeLike
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (Old T : Stage K D)
    (S : Set Old.Carrier) (hS : Old.system.toStructure.IsClosed S)
    (f : FunctionalPartite.Embedding (Old.system.induce S hS) T.system)
    (α : Structure.Embedding A D)
    (hSupport : ∀ x : Old.Carrier, x ∈ S →
      ∃ a : U, Old.system.part x = α a)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph B.graph D.graph (n - 1))
    (hOld : RelStructure.LocallyTreeLike A.graph B.graph
      Old.system.toStructure.graph n)
    (hCore : RelStructure.LocallyTreeLike A.graph B.graph
      T.system.toStructure.graph n) :
    RelStructure.LocallyTreeLike A.graph B.graph
      (T.attach hK Old.system Old.isPartite Old.mem S hS f).system.toStructure.graph n := by
  classical
  let maps :
      PUnit.{v+1} →
        RelStructure.Embedding (Old.system.toStructure.graph.induce S)
          T.system.toStructure.graph :=
    fun _ => Structure.Attachment.attachingGraphMap
      Old.system.toStructure S hS T.system.toStructure f.toEmbedding
  let R : Stage K D :=
    T.attach hK Old.system Old.isPartite Old.mem S hS f
  let hIso : RelStructure.Iso R.system.toStructure.graph
      (RelStructure.Attachment.attach Old.system.toStructure.graph S
        T.system.toStructure.graph maps) :=
    T.attachGraphIso hK Old.system Old.isPartite Old.mem S hS f
  have hNative :
      R.system.toStructure.graph.IsHomomorphismEmbedding D.graph
        R.system.part :=
    R.isPartite.graphHomomorphismEmbedding
  let p : RelStructure.Attachment.Vertex S
        (W := T.Carrier) (I := PUnit.{v+1}) → P :=
    R.system.part ∘ hIso.toEquiv.symm
  have hp :
      (RelStructure.Attachment.attach Old.system.toStructure.graph S
        T.system.toStructure.graph maps).IsHomomorphismEmbedding D.graph p :=
    hNative.transportIso hIso
  have hSupportRel :
      ∀ (i : PUnit.{v+1}) (x : Old.Carrier), x ∈ S →
        ∃ a : U,
          p (RelStructure.Attachment.copyMap
            Old.system.toStructure.graph S T.system.toStructure.graph maps i x) =
              α.graph a := by
    intro i x hx
    cases i
    obtain ⟨a, ha⟩ := hSupport x hx
    refine ⟨a, ?_⟩
    have hcopy :
        R.system.part
          (Structure.Attachment.copyMap
            Old.system.toStructure S hS T.system.toStructure
            (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit x) =
              Old.system.part x := by
      exact FunctionalPartite.Attachment.part_copyMap
        Old.system S hS T.system
        (fun _ : PUnit.{v+1} => f) PUnit.unit x
    calc
      p (RelStructure.Attachment.copyMap
          Old.system.toStructure.graph S T.system.toStructure.graph
          maps PUnit.unit x) =
        R.system.part (Structure.Attachment.copyMap
          Old.system.toStructure S hS T.system.toStructure
          (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit x) := by
          change R.system.part
              (RelStructure.Attachment.copyMap
                Old.system.toStructure.graph S T.system.toStructure.graph
                maps PUnit.unit x) =
            R.system.part
              (Structure.Attachment.copyMap
                Old.system.toStructure S hS T.system.toStructure
                (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit x)
          exact congrArg R.system.part
            (Structure.Attachment.copyMap_graph_eq
              Old.system.toStructure S hS T.system.toStructure
              (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit x).symm
      _ = Old.system.part x := hcopy
      _ = α a := ha
  have hGraph :
      RelStructure.LocallyTreeLike A.graph B.graph
        (RelStructure.Attachment.attach Old.system.toStructure.graph S
          T.system.toStructure.graph maps) n :=
    RelStructure.Attachment.locallyTreeLike_of_projected_support
      A.graph B.graph D.graph
      Old.system.toStructure.graph T.system.toStructure.graph
      S maps hA eAB.graph n hn hD hOld hCore
      p hp α.graph hSupportRel
  exact hGraph.pullback_embedding hIso.toEmbedding

end

end StructuralRamsey.FunctionalPartite.EHN

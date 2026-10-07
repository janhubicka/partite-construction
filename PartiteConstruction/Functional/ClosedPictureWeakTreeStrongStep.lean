import PartiteConstruction.Functional.ClosedPictureWeakTreeStrong
import PartiteConstruction.Functional.ClosedPicture

/-! # U-closed Hales--Jewett Pictures preserve the iterable weak invariant

The strong relational locally tree-like invariant includes the control of
ambient A-copies needed to iterate.  Hereditary irreducibility of the graph
control is assumed explicitly, just as in the verified relational theorem.

Function outputs are handled by the U-closed Hales--Jewett construction,
but the local tree conclusion is a graph-level weak-substructure assertion.
-/

namespace StructuralRamsey.Partite.Closed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {A : RelStructure L.graph U}
variable {D : RelStructure L.graph P}
variable {B : Partite.System L.graph P V}
variable {α : RelStructure.ClosedEmbedding A D}

/-- One actual closed Picture step retains all strong weak-substructure
control at the same vertex rank, including the closed Picture property. -/
theorem pictureLemma_withStrongTree
    {VB : Type v} [Finite VB]
    (Base : RelStructure L.graph VB)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A Base D (n - 1))
    (hOld : RelStructure.LocallyTreeLike A Base B.toRelStructure n)
    (hB : B.IsPartiteOver D)
    (hU : B.FunctionOutputTransversal)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D ∧
      C.FunctionOutputTransversal ∧
      PictureProperty A B α C κ ∧
      RelStructure.LocallyTreeLike A Base C.toRelStructure n := by
  classical
  let αinj := α.toEmbedding.toFunctionEmbedding
  let R := B.restrict αinj
  have hR : R.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver D B A hB α.toEmbedding
  have hRU : R.FunctionOutputTransversal := by
    intro F x y z hy hz hp
    have hy0 :
        B.rel (.inr F)
          (Subtype.val ∘ Structure.funcTuple x y) := hy
    have hz0 :
        B.rel (.inr F)
          (Subtype.val ∘ Structure.funcTuple x z) := hz
    have hty :
        Subtype.val ∘ Structure.funcTuple x y =
          Structure.funcTuple (Subtype.val ∘ x) y.1 :=
      Structure.comp_funcTuple Subtype.val x y
    have htz :
        Subtype.val ∘ Structure.funcTuple x z =
          Structure.funcTuple (Subtype.val ∘ x) z.1 :=
      Structure.comp_funcTuple Subtype.val x z
    have hyB :
        B.rel (.inr F)
          (Structure.funcTuple (Subtype.val ∘ x) y.1) :=
      Eq.mp (congrArg (fun t => B.rel (.inr F) t) hty) hy0
    have hzB :
        B.rel (.inr F)
          (Structure.funcTuple (Subtype.val ∘ x) z.1) :=
      Eq.mp (congrArg (fun t => B.rel (.inr F) t) htz) hz0
    have hpB : B.part y.1 = B.part z.1 :=
      (B.restrictedPart_spec αinj y).symm.trans
        ((congrArg (fun q => α q) hp).trans
          (B.restrictedPart_spec αinj z))
    apply Subtype.ext
    exact hU F (Subtype.val ∘ x) y.1 z.1 hyB hzB hpB
  obtain ⟨N, hN, hPowerU, hArrow⟩ :=
    Closed.Induced.partiteLemma (A := A) (B := R) hR hRU κ
  let E := Partite.Induced.power R N
  let C := build A D B α E
  have hE : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  have hCorePartite :
      (E.relabel αinj).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hE α.toEmbedding
  have hCPartite : C.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      B (B.support αinj) (E.relabel αinj)
      (fun f : Closed.Embedding R E =>
        (attachingMap (A := A) (D := D) (B := B)
          (α := α) E f).1)
      hB hCorePartite
  have hCoreU : (E.relabel αinj).FunctionOutputTransversal := by
    intro F x y z hy hz hp
    exact hPowerU F x y z hy hz (α.toEmbedding.injective hp)
  have hCU : C.FunctionOutputTransversal := by
    exact Closed.Attachment.uTransversal
      (B := B) (S := B.support αinj)
      (D := E.relabel αinj)
      (f := fun f : Closed.Embedding R E =>
        attachingMap (A := A) (D := D) (B := B)
          (α := α) E f)
      (supportClosed (A := A) (D := D) (B := B) (α := α) hB)
      hU hCoreU
  have hStrong :
      RelStructure.LocallyTreeLike A Base C.toRelStructure n :=
    locallyTreeLike_weakStep
      A Base D B α hA eAB n hn hD hOld hB N hN
  exact ⟨Vertex A D B α E,
    inferInstance, C, hCPartite, hCU,
    property A D B α E hB κ hArrow, hStrong⟩


end StructuralRamsey.Partite.Closed.Picture

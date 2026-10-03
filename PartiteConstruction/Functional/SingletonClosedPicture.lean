import PartiteConstruction.Functional.SingletonPartite
import PartiteConstruction.Functional.ClosedPicture

/-! # Closed Picture lemma preserving singleton-valuedness

This is the partial-function strengthening of the checked closed-alpha Picture
lemma.  Coordinate powers and closed free attachment preserve the invariant
that every function input has at most one output.
-/
namespace StructuralRamsey.Partite.Closed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V W : Type v}

/-- The explicit closed Picture attachment is singleton-valued whenever both
the old picture and the Hales--Jewett core are singleton-valued. -/
theorem build_singleValued
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hBPartite : B.IsPartiteOver D)
    (hB : B.FunctionOutputSingleValued)
    (hE : E.FunctionOutputSingleValued) :
    (build A D B α E).FunctionOutputSingleValued := by
  let αinj := α.toEmbedding.toFunctionEmbedding
  have hCore :
      (E.relabel αinj).FunctionOutputSingleValued :=
    Partite.System.relabel_singleValued αinj hE
  exact Partite.Closed.Attachment.singleValued
    (B := B)
    (S := B.support αinj)
    (D := E.relabel αinj)
    (f := fun f : Partite.Closed.Embedding
      (B.restrict αinj) E =>
        attachingMap A D B α E f)
    (supportClosed A D B α hBPartite)
    hB hCore

/-- Closed-alpha Picture lemma with the stronger global partial-function
invariant. -/
theorem pictureLemma_singleValued
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (hBPartite : B.IsPartiteOver D)
    (hB : B.FunctionOutputSingleValued)
    [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D ∧
      C.FunctionOutputSingleValued ∧
      PictureProperty A B α C κ := by
  classical
  let αinj := α.toEmbedding.toFunctionEmbedding
  let R := B.restrict αinj
  have hR : R.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver
      D B A hBPartite α.toEmbedding
  have hRSingle : R.FunctionOutputSingleValued :=
    Partite.System.restrict_singleValued αinj hB
  have hRU : R.FunctionOutputTransversal :=
    hRSingle.uTransversal
  obtain ⟨N, hN, _hPowerU, hArrow⟩ :=
    Closed.Induced.partiteLemma
      (A := A) (B := R) hR hRU κ
  let E := Partite.Induced.power R N
  have hESingle : E.FunctionOutputSingleValued :=
    Closed.Induced.power_singleValued hN hRSingle
  let C := build A D B α E
  have hEPartite : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  have hCorePartite :
      (E.relabel αinj).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hEPartite α.toEmbedding
  have hCPartite : C.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      B (B.support αinj) (E.relabel αinj)
      (fun f : Partite.Closed.Embedding R E =>
        (attachingMap (A := A) (D := D) (B := B)
          (α := α) E f).1)
      hBPartite hCorePartite
  have hCSingle : C.FunctionOutputSingleValued :=
    build_singleValued A D B α E hBPartite hB hESingle
  exact ⟨Vertex A D B α E,
    inferInstance, C, hCPartite, hCSingle,
    property A D B α E hBPartite κ hArrow⟩

end StructuralRamsey.Partite.Closed.Picture

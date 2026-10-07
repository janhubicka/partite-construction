import PartiteConstruction.Functional.ClosedPictureWeakTree

/-! # Closed Picture lemma preserving weak graph-tree local completions

An actual U-closed Picture step chooses its Hales--Jewett power, attaches
the U-closed (rather than all relational) old copies, and preserves the
complete functional Ramsey/partite construction invariants.  The attachment
reindexing theorem transfers the relational weak-substructure local bound to
this same chosen Picture, with **no function closure of the test set**.

The output is graph-tree completable on arbitrary weak vertex tests, not yet
a full functional strict-tree completion.
-/

namespace StructuralRamsey.Partite.Closed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {A : RelStructure L.graph U}
variable {D : RelStructure L.graph P}
variable {B : Partite.System L.graph P V}
variable {α : RelStructure.ClosedEmbedding A D}

/-- The U-closed Hales--Jewett Picture preserves the local graph-tree
completion at level n along with U-transversality and the closed Picture
colouring property. -/
/-- The valid closed-alpha induced Picture Lemma with closures. -/
theorem pictureLemma_withLocal
    {VB : Type v}
    (Base : RelStructure L.graph VB)
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := Base) id (n - 1))
    (hLocal : RelStructure.LocallyTreeCompletable Base B.toRelStructure n)
    (hB : B.IsPartiteOver D)
    (hU : B.FunctionOutputTransversal)
    [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D ∧
      C.FunctionOutputTransversal ∧
      PictureProperty A B α C κ ∧
      RelStructure.LocallyTreeCompletable Base C.toRelStructure n := by
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
  have hTree : RelStructure.LocallyTreeCompletable Base C.toRelStructure n :=
    locallyTreeCompletable_projectedHistory
      A Base D B α hA eAB n hn hD hLocal hB N hN
  exact ⟨Vertex A D B α E,
    inferInstance, C, hCPartite, hCU,
    property A D B α E hB κ hArrow, hTree⟩


end StructuralRamsey.Partite.Closed.Picture

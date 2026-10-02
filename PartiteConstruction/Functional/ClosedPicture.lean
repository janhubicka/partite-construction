import PartiteConstruction.Functional.ClosedPartite
import PartiteConstruction.Functional.ClosedOperations
import PartiteConstruction.Functional.ClosedAttachment
import PartiteConstruction.Partite.InducedAttachment
import PartiteConstruction.Partite.Picture

/-! # Closed induced Picture Lemma

This is the valid U-closed Picture step.  The prescribed projection
alpha : A -> D is assumed U-closed. Then the selected support is U-closed,
closed Hales--Jewett embeddings of the restriction may be extended by free
attachment, the core and attached copies remain U-closed, and
U-transversality is preserved.
-/
namespace StructuralRamsey.Partite.Closed

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V W : Type v}

/-- U-closed copies with prescribed projection. -/
def ProjectedEmbedding
    (A : RelStructure L.graph U)
    (B : Partite.System L.graph P V)
    (α : U → P) :=
  {e : RelStructure.ClosedEmbedding A B.toRelStructure //
    ∀ x, B.part (e x) = α x}

namespace ProjectedEmbedding

variable {A : RelStructure L.graph U}
  {B : Partite.System L.graph P V} {α : U → P}

@[ext] theorem ext {f g : ProjectedEmbedding A B α}
    (h : ∀ x, f.1 x = g.1 x) : f = g := by
  apply Subtype.ext
  exact RelStructure.ClosedEmbedding.ext h

def comp {X : Type v} {C : Partite.System L.graph P X}
    (e : ProjectedEmbedding A B α)
    (f : Closed.Embedding B C) :
    ProjectedEmbedding A C α :=
  ⟨RelStructure.ClosedEmbedding.comp f.toRelClosed e.1,
    fun x => (f.1.map_part (e.1 x)).trans (e.2 x)⟩

end ProjectedEmbedding

def PictureProperty
    (A : RelStructure L.graph U)
    (B : Partite.System L.graph P V)
    (α : U → P)
    {X : Type v} (C : Partite.System L.graph P X)
    (κ : Type*) : Prop :=
  ∀ χ : ProjectedEmbedding A C α → κ,
    ∃ f : Closed.Embedding B C,
      ∀ e₁ e₂ : ProjectedEmbedding A B α,
        χ (e₁.comp f) = χ (e₂.comp f)

namespace Picture

variable (A : RelStructure L.graph U)
variable (D : RelStructure L.graph P)
variable (B : Partite.System L.graph P V)
variable (α : RelStructure.ClosedEmbedding A D)

/-- A prescribed U-closed copy restricts to a U-closed partite embedding into
the selected parts. -/
def restrictEmbedding
    (e : ProjectedEmbedding A B α) :
    Closed.Embedding
      (Partite.transversal A)
      (B.restrict α.toEmbedding.toFunctionEmbedding) := by
  let αinj := α.toEmbedding.toFunctionEmbedding
  let pe : Partite.Embedding
      (Partite.transversal A) (B.restrict αinj) := {
    toFun := fun x => ⟨e.1 x, x, (e.2 x).symm⟩
    injective := by
      intro x y h
      exact e.1.toEmbedding.injective (congrArg Subtype.val h)
    map_rel_iff := by
      intro R x
      exact e.1.toEmbedding.map_rel_iff R x
    map_part := by
      intro x
      apply α.toEmbedding.injective
      exact
        (B.restrictedPart_spec αinj
          ⟨e.1 x, x, (e.2 x).symm⟩).trans (e.2 x)
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hy0 :
      B.rel (.inr F)
        (Subtype.val ∘
          Structure.funcTuple (pe ∘ x) y) := hy
  have htuple :
      Subtype.val ∘ Structure.funcTuple (pe ∘ x) y =
        Structure.funcTuple (e.1 ∘ x) y.1 := by
    calc
      Subtype.val ∘ Structure.funcTuple (pe ∘ x) y =
          Structure.funcTuple
            (Subtype.val ∘ (pe ∘ x)) y.1 :=
        Structure.comp_funcTuple Subtype.val (pe ∘ x) y
      _ = Structure.funcTuple (e.1 ∘ x) y.1 := rfl
  have hyB :
      B.rel (.inr F)
        (Structure.funcTuple (e.1 ∘ x) y.1) :=
    Eq.mp (congrArg (fun t => B.rel (.inr F) t) htuple) hy0
  obtain ⟨z, hz, hzy⟩ := e.1.closed F x y.1 hyB
  have hzSupport :
      e.1 z ∈ B.support αinj := ⟨z, (e.2 z).symm⟩
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  exact hzy

variable {A D B α}
variable (E : Partite.System L.graph U W)

/-- A closed embedding of the restriction into the power gives a closed
attaching map on the underlying selected support. -/
def attachingMap
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (f : Closed.Embedding (B.restrict α.toEmbedding.toFunctionEmbedding) E) :
    Closed.Embedding
      (B.induce (B.support α.toEmbedding.toFunctionEmbedding))
      (E.relabel α.toEmbedding.toFunctionEmbedding) :=
  ⟨Partite.Picture.attachingMap
      B α.toEmbedding.toFunctionEmbedding E f.1,
    f.2⟩

abbrev Vertex
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W) :=
  Closed.Attachment.Vertex
    (B.support α.toEmbedding.toFunctionEmbedding)
    W
    (Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E)

noncomputable def build
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W) :
    Partite.System L.graph P (Vertex A D B α E) :=
  Closed.Attachment.attach
    B (B.support α.toEmbedding.toFunctionEmbedding)
    (E.relabel α.toEmbedding.toFunctionEmbedding)
    (fun f : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
        attachingMap A D B α E f)

theorem supportClosed
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (hB : B.IsPartiteOver D) :
    RelStructure.FunctionClosedSet B.toRelStructure
      (B.support α.toEmbedding.toFunctionEmbedding) :=
  Closed.support_functionClosed D B hB A α

noncomputable def coreEmbedding
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hB : B.IsPartiteOver D) :
    Closed.Embedding
      (E.relabel α.toEmbedding.toFunctionEmbedding)
      (build A D B α E) := by
  let maps :=
    fun f : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
        attachingMap A D B α E f
  let pe :=
    Partite.Attachment.coreEmbedding
      B (B.support α.toEmbedding.toFunctionEmbedding)
      (E.relabel α.toEmbedding.toFunctionEmbedding)
      (fun i => (maps i).1)
  refine ⟨pe, ?_⟩
  exact Closed.Attachment.core_closed
    (B := B)
    (S := B.support α.toEmbedding.toFunctionEmbedding)
    (D := E.relabel α.toEmbedding.toFunctionEmbedding)
    (f := maps) (supportClosed A D B α hB)

noncomputable def copyEmbedding
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hB : B.IsPartiteOver D)
    (f : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E) :
    Closed.Embedding B (build A D B α E) := by
  let maps :=
    fun g : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
        attachingMap A D B α E g
  let pe :=
    Partite.Attachment.copyEmbedding
      B (B.support α.toEmbedding.toFunctionEmbedding)
      (E.relabel α.toEmbedding.toFunctionEmbedding)
      (fun i => (maps i).1) f
  refine ⟨pe, ?_⟩
  exact Closed.Attachment.copy_closed
    (B := B)
    (S := B.support α.toEmbedding.toFunctionEmbedding)
    (D := E.relabel α.toEmbedding.toFunctionEmbedding)
    (f := maps) (supportClosed A D B α hB) f

noncomputable def coreLetter
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hB : B.IsPartiteOver D)
    (e : Closed.Embedding (Partite.transversal A) E) :
    ProjectedEmbedding A (build A D B α E) α := by
  let ce := coreEmbedding A D B α E hB
  let comp := RelStructure.ClosedEmbedding.comp ce.toRelClosed e.toRelClosed
  refine ⟨comp, ?_⟩
  intro x
  change
    (build A D B α E).part
      (Partite.Attachment.coreEmbedding
        B (B.support α.toEmbedding.toFunctionEmbedding)
        (E.relabel α.toEmbedding.toFunctionEmbedding)
        (fun f : Closed.Embedding
          (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
            (attachingMap A D B α E f).1)
        (e.1 x)) =
      α x
  exact congrArg α.toEmbedding (e.1.map_part x)

theorem copy_comp_restrict
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hB : B.IsPartiteOver D)
    (f : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E)
    (e : ProjectedEmbedding A B α) :
    e.comp (copyEmbedding A D B α E hB f) =
      coreLetter A D B α E hB
        (Closed.Embedding.comp f (restrictEmbedding A D B α e)) := by
  apply ProjectedEmbedding.ext
  intro x
  change
    Partite.Attachment.copyEmbedding
      B (B.support α.toEmbedding.toFunctionEmbedding)
      (E.relabel α.toEmbedding.toFunctionEmbedding)
      (fun g : Closed.Embedding
        (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
          (attachingMap A D B α E g).1)
      f (e.1 x) =
    Partite.Attachment.coreEmbedding
      B (B.support α.toEmbedding.toFunctionEmbedding)
      (E.relabel α.toEmbedding.toFunctionEmbedding)
      (fun g : Closed.Embedding
        (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
          (attachingMap A D B α E g).1)
      (f.1 ⟨e.1 x, x, (e.2 x).symm⟩)
  exact Partite.Attachment.copy_extends
    B (B.support α.toEmbedding.toFunctionEmbedding)
    (E.relabel α.toEmbedding.toFunctionEmbedding)
    (fun g : Closed.Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) E =>
        (attachingMap A D B α E g).1)
    f ⟨e.1 x, x, (e.2 x).symm⟩

/-- Closed Picture property from a closed Ramsey core. -/
theorem property
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W)
    (hB : B.IsPartiteOver D)
    (κ : Type*)
    (hE : Closed.Arrow
      (Partite.transversal A)
      (B.restrict α.toEmbedding.toFunctionEmbedding)
      E κ) :
    PictureProperty A B α (build A D B α E) κ := by
  intro χ
  obtain ⟨f, hf⟩ :=
    hE (fun e => χ (coreLetter A D B α E hB e))
  refine ⟨copyEmbedding A D B α E hB f, ?_⟩
  intro e₁ e₂
  rw [copy_comp_restrict A D B α E hB,
    copy_comp_restrict A D B α E hB]
  exact hf
    (restrictEmbedding A D B α e₁)
    (restrictEmbedding A D B α e₂)

/-- The valid closed-alpha induced Picture Lemma with closures. -/
theorem pictureLemma
    (hB : B.IsPartiteOver D)
    (hU : B.FunctionOutputTransversal)
    [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ (X : Type v) (_ : Finite X)
      (C : Partite.System L.graph P X),
      C.IsPartiteOver D ∧
      C.FunctionOutputTransversal ∧
      PictureProperty A B α C κ := by
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
  exact ⟨Vertex A D B α E,
    inferInstance, C, hCPartite, hCU,
    property A D B α E hB κ hArrow⟩

end Picture
end StructuralRamsey.Partite.Closed

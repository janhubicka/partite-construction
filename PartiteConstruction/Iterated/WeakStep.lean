import PartiteConstruction.Iterated.GenericProjectedAttachmentStep
import PartiteConstruction.Partite.InducedPicture
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Iterated.ProjectedGlue
import PartiteConstruction.Iterated.WeakLocalTreeLike
import PartiteConstruction.Iterated.ControlCompletion

/-! # One-step weak local tree-likeness for the induced picture construction

On graph encodings this is exactly the weak-substructure induction for function structures.

This formalizes the strengthened tree invariant when the control structure A
is hereditarily irreducible.  For a finite test set S, either the projection
has size below n and the base-D hypothesis applies directly, or the projection
is injective on S.  In the latter case S lies wholly in the power core,
wholly in one attached copy, or decomposes as a genuine free amalgam whose
two projected sides have size at most n-1.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X : Type v}

/-- One canonical induced Picture step preserves local tree-likeness,
provided every induced substructure of A is irreducible. -/
theorem canonicalStep_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    [Finite U] [Finite V] [Finite P] [Finite X]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hC₀ : RelStructure.LocallyTreeLike A B C₀.toRelStructure n)
    (hPartite : C₀.IsPartiteOver D)
    (N : ℕ) (hN : 0 < N) :
    RelStructure.LocallyTreeLike A B
      (Partite.Picture.build C₀ α.toFunctionEmbedding
        (Partite.Induced.power
          (C₀.restrict α.toFunctionEmbedding) N)).toRelStructure n := by
  classical
  let αf := α.toFunctionEmbedding
  let R := C₀.restrict αf
  have hR : R.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver D C₀ A hPartite α
  let E := Partite.Induced.power R N
  have hE : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  let Core := E.relabel αf
  have hCorePartite : Core.IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver (A := A) (B := E) hE α
  let C₁ := Partite.Picture.build C₀ αf E
  have hC₁Partite : C₁.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      C₀ (C₀.support αf) Core
      (Partite.Picture.attachingMap C₀ αf E) hPartite hCorePartite
  have hCoreLTL :
      RelStructure.LocallyTreeLike A B Core.toRelStructure n := by
    change RelStructure.LocallyTreeLike A B E.toRelStructure n
    exact RelStructure.LocallyTreeLike.of_homEmbedding_to_base
      hA.irreducible eAB E.part hE n

  let Supp := C₀.support αf
  let maps : Partite.Embedding R E →
      RelStructure.Embedding (C₀.toRelStructure.induce Supp)
        Core.toRelStructure :=
    fun i => (Partite.Picture.attachingMap C₀ αf E i).toEmbedding
  have hProjection :
      (RelStructure.Attachment.attach
        C₀.toRelStructure Supp Core.toRelStructure maps).IsHomomorphismEmbedding
          D C₁.part := by
    simpa [C₁, Partite.Picture.build, Partite.Attachment.attach,
      Supp, maps] using hC₁Partite
  have hSupport :
      ∀ (i : Partite.Embedding R E) (x : X), x ∈ Supp →
        ∃ a : U,
          C₁.part
            (RelStructure.Attachment.copyMap
              C₀.toRelStructure Supp Core.toRelStructure maps i x) = α a := by
    intro i x hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    calc
      C₁.part
          (RelStructure.Attachment.copyMap
            C₀.toRelStructure Supp Core.toRelStructure maps i x) =
          C₀.part x := by
            simpa [C₁, Partite.Picture.build, Partite.Attachment.attach,
              Supp, maps] using
              (Partite.Attachment.part_copyMap C₀
                (C₀.support αf) Core
                (Partite.Picture.attachingMap C₀ αf E) i x)
      _ = α a := ha.symm
  have hGeneric :
      RelStructure.LocallyTreeLike A B
        (RelStructure.Attachment.attach
          C₀.toRelStructure Supp Core.toRelStructure maps) n :=
    RelStructure.Attachment.locallyTreeLike_of_projected_support
      A B D C₀.toRelStructure Core.toRelStructure
      Supp maps hA eAB n hn hD hC₀ hCoreLTL
      C₁.part hProjection α hSupport
  simpa [C₁, Partite.Picture.build, Partite.Attachment.attach,
    Supp, maps] using hGeneric

end StructuralRamsey.Partite.Iterated

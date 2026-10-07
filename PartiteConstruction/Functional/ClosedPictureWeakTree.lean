import PartiteConstruction.Relational.AttachmentReindex
import PartiteConstruction.Functional.ClosedPicture
import PartiteConstruction.Iterated.WeakStepTreeCompletion

/-! # Weak local tree induction through a closed functional Picture step

For set-valued functions, a genuinely U-closed A-copy is required for the
functional partite lemma and Picture construction.  The U-closed Picture
uses the same coordinate power as the underlying ordinary relational Picture,
but attaches old copies only along U-closed embeddings of the selected
support.  These embeddings form a subfamily of all relational embeddings.

The restricted attachment embeds as an **induced relational substructure**
of the ordinary attachment.  Therefore the existing vertex-cardinality
induction on arbitrary induced graph substructures transfers to the actual
closed Picture stage.  No function-closure of a tested finite set is taken,
so the local size bound does not grow.

This is a graph-level weak-substructure theorem.  Recovering a strict
functional tree and full functional homomorphism-embedding still requires
output-closure certificates.
-/

namespace StructuralRamsey.Partite.Closed.Picture

open StructuralRamsey.RelStructure

universe u v

variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The U-closed Picture attaches a subfamily of the ordinary relational
copies.  The resulting inclusion is an induced relational embedding, even
though the entire closed Picture need not be function-closed in the ordinary
relational Picture target. -/
noncomputable def toOrdinaryRelEmbedding
    (A : RelStructure L.graph U)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    (E : Partite.System L.graph U W) :
    RelStructure.Embedding
      (build A D B α E).toRelStructure
      (Partite.Picture.build B α.toEmbedding.toFunctionEmbedding E).toRelStructure := by
  let αf := α.toEmbedding.toFunctionEmbedding
  let R := B.restrict αf
  let index : Closed.Embedding R E ↪ Partite.Embedding R E := {
    toFun := Subtype.val
    inj' := Subtype.val_injective
  }
  let fclosed :
      Closed.Embedding R E →
        RelStructure.Embedding
          (B.toRelStructure.induce (B.support αf))
          (E.relabel αf).toRelStructure :=
    fun e => (Partite.Picture.attachingMap B αf E e.1).toEmbedding
  let fall :
      Partite.Embedding R E →
        RelStructure.Embedding
          (B.toRelStructure.induce (B.support αf))
          (E.relabel αf).toRelStructure :=
    fun e => (Partite.Picture.attachingMap B αf E e).toEmbedding
  have hf : ∀ i, fclosed i = fall (index i) := by
    intro i
    rfl
  change RelStructure.Embedding
    (RelStructure.Attachment.attach B.toRelStructure
      (B.support αf) (E.relabel αf).toRelStructure fclosed)
    (RelStructure.Attachment.attach B.toRelStructure
      (B.support αf) (E.relabel αf).toRelStructure fall)
  exact RelStructure.Attachment.reindexEmbedding fclosed fall index hf

/-- Every U-closed functional Picture step preserves the relational
graph-tree completion invariant for weak substructures on at most n vertices,
assuming the control D has projected-history completion at the previous
level n-1.  The geometric argument uses the actual U-closed Picture and
does not alter function-value sets of the tested vertex restriction. -/
theorem locallyTreeCompletable_projectedHistory
    (A : RelStructure L.graph U)
    (Base : RelStructure L.graph VB)
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (α : RelStructure.ClosedEmbedding A D)
    [Finite U] [Finite VB] [Finite P] [Finite V]
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := Base) id (n - 1))
    (hB : RelStructure.LocallyTreeCompletable Base B.toRelStructure n)
    (hPartite : B.IsPartiteOver D)
    (N : ℕ) (hN : 0 < N) :
    let E := Partite.Induced.power
      (B.restrict α.toEmbedding.toFunctionEmbedding) N
    RelStructure.LocallyTreeCompletable Base
      (build A D B α E).toRelStructure n := by
  let E := Partite.Induced.power
    (B.restrict α.toEmbedding.toFunctionEmbedding) N
  have hOrd :
      RelStructure.LocallyTreeCompletable Base
        (Partite.Picture.build
          B α.toEmbedding.toFunctionEmbedding E).toRelStructure n :=
    Partite.Iterated.canonicalStep_locallyTreeCompletable_projectedHistory
      A Base D B α.toEmbedding hA eAB n hn hD hB hPartite N hN
  exact hOrd.pullback_embedding (toOrdinaryRelEmbedding A D B α E)

end StructuralRamsey.Partite.Closed.Picture

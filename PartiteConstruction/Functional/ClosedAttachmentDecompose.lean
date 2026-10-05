import PartiteConstruction.Functional.ClosedAttachment
import PartiteConstruction.Functional.Closed
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-! # Closed tests in functional attachments

The relational attachment-decomposition lemma works for every induced test
set.  For the functional local-tree argument the tested set is a genuine
closed substructure.  In a closed attachment its chosen-copy piece and the
complementary rest are again function-closed, so the relational decomposition
decodes to a genuine full free amalgam.
-/

namespace StructuralRamsey.Partite.Closed.Attachment

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V W I : Type v}

variable (B : Partite.System L.graph P V) (S : Set V)
variable (D : Partite.System L.graph P W)
variable (f : I → Partite.Closed.Embedding (B.induce S) D)

abbrev RAttach :=
  Partite.Closed.Attachment.attach B S D f

abbrev AV :=
  Partite.Attachment.Vertex S (W := W) (I := I)

variable (T : Set (AV (S := S) (W := W) (I := I)))
variable (i : I)

/-- The chosen-copy part of a closed test is function-closed. -/
theorem piece_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hT : RelStructure.FunctionClosedSet
      (RAttach B S D f).toRelStructure T) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.pieceSet
        B.toRelStructure S D.toRelStructure
        (fun j => (f j).1.toEmbedding) T i) := by
  classical
  let Whole := (RAttach B S D f).toRelStructure
  let copy : Partite.Closed.Embedding B (RAttach B S D f) :=
    ⟨Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i,
      Partite.Closed.Attachment.copy_closed
        (B := B) (S := S) (D := D) (f := f) hS i⟩
  let CopyRange : Set (AV (S := S) (W := W) (I := I)) :=
    Set.range copy
  have hCopyRange : RelStructure.FunctionClosedSet Whole CopyRange := by
    exact copy.toRelClosed.toEmbedding.range_functionClosed copy.toRelClosed.closed
  intro F x y hy hx
  have hyWhole :
      Whole.rel (.inr F)
        (Structure.funcTuple (Subtype.val ∘ x) y.1) := by
    exact hy
  have hxT : ∀ k, (x k).1 ∈ T := fun k => (x k).1.2
  have hyT : y.1 ∈ T :=
    hT F (Subtype.val ∘ x) y.1 hyWhole hxT
  have hxCopy : ∀ k, (x k).1 ∈ CopyRange := by
    intro k
    rcases (x k).2 with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  have hyCopy : y.1 ∈ CopyRange :=
    hCopyRange F (fun k => (x k).1) y.1 hyWhole hxCopy
  rcases hyCopy with ⟨a, ha⟩
  refine ⟨⟨y.1, hyT⟩, ?_, rfl⟩
  exact ⟨a, ha.symm⟩

/-- The rest obtained by deleting the chosen copy's exclusive vertices is
function-closed inside a closed test. -/
theorem rest_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hT : RelStructure.FunctionClosedSet
      (RAttach B S D f).toRelStructure T) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.restSet
        (W := W) (I := I) S T i) := by
  classical
  let Whole := (RAttach B S D f).toRelStructure
  let maps :
      I → RelStructure.Embedding
        (B.toRelStructure.induce S) D.toRelStructure :=
    fun j => {
      toFun := f j
      injective := (f j).1.toEmbedding.injective
      map_rel_iff := (f j).1.toEmbedding.map_rel_iff
    }
  intro F x y hy hx
  have hyWhole :
      Whole.rel (.inr F)
        (Structure.funcTuple (Subtype.val ∘ x) y.1) := hy
  have hxT : ∀ k, (x k).1 ∈ T := fun k => (x k).1.2
  have hyT : y.1 ∈ T :=
    hT F (Subtype.val ∘ x) y.1 hyWhole hxT
  refine ⟨⟨y.1, hyT⟩, ?_, rfl⟩
  intro hout
  rcases hout with ⟨out, houtEq⟩
  -- An exclusive output of copy i forces the whole graph tuple into copy i.
  have hlast :
      (Structure.funcTuple
          (Subtype.val ∘ x) y.1)
          (Fin.last (L.funcArity F)) =
        Sum.inr (i, out) := by
    rw [Structure.funcTuple_last]
    exact houtEq
  obtain ⟨q, hq, heq⟩ :=
    RelStructure.Attachment.relation_eq_copy_of_contains_outside
      (B := B.toRelStructure) (S := S)
      (D := D.toRelStructure) (f := maps)
      hyWhole (Fin.last (L.funcArity F)) i out hlast
  let args : Fin (L.funcArity F) → V :=
    fun k => q (Fin.castSucc k)
  have hargsInCopy :
      ∀ k, (x k).1 =
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure maps i (args k) := by
    intro k
    have hk := congrFun heq (Fin.castSucc k)
    rw [Structure.funcTuple_castSucc] at hk
    exact hk
  have hargsS : ∀ k, args k ∈ S := by
    intro k
    by_contra hkS
    have hexcl :
        RelStructure.Attachment.OutsideAt
          (W := W) (I := I) S i (x k).1 := by
      refine ⟨⟨args k, hkS⟩, ?_⟩
      rw [hargsInCopy k]
      exact RelStructure.Attachment.copyMap_not_mem
        (B := B.toRelStructure) (S := S)
        (D := D.toRelStructure) (f := maps)
        i (args k) hkS
    exact (x k).2.2 hexcl
  let outB : V := q (Fin.last (L.funcArity F))
  have hrelB :
      B.rel (.inr F) (Structure.funcTuple args outB) := by
    have heta : Structure.funcTuple args outB = q := by
      simpa [args, outB, Language.graph] using
        (Structure.funcTuple_eta (t := q))
    rw [heta]
    exact hq
  have houtS : outB ∈ S := hS F args outB hrelB hargsS
  have houtTuple := congrFun heq (Fin.last (L.funcArity F))
  rw [Structure.funcTuple_last] at houtTuple
  have houtCore :
      y.1 =
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure maps i outB :=
    houtTuple
  rw [RelStructure.Attachment.copyMap_mem
      (B := B.toRelStructure) (S := S)
      (D := D.toRelStructure) (f := maps)
      i outB houtS] at houtCore
  rw [houtEq] at houtCore
  simp at houtCore

/-- The overlap of the chosen piece and rest is closed. -/
theorem overlap_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hT : RelStructure.FunctionClosedSet
      (RAttach B S D f).toRelStructure T) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.overlapSet
        (W := W) (I := I)
        B.toRelStructure S D.toRelStructure
        (fun j => (f j).1.toEmbedding) T i) := by
  intro F x y hy hx
  exact ⟨
    piece_functionClosed B S D f T i hS hT
      F x y hy (fun k => (hx k).1),
    rest_functionClosed B S D f T i hS hT
      F x y hy (fun k => (hx k).2)⟩

end StructuralRamsey.Partite.Closed.Attachment

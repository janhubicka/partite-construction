import PartiteConstruction.Functional.ClosedAttachment
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-! # Closed tests in functional attachments

The relational attachment-decomposition lemma works for every induced test
set.  For the functional local-tree argument the tested set is a genuine
function-closed substructure.  In a closed attachment, its chosen-copy piece,
the complementary rest, and hence their overlap are again function-closed.
-/

namespace StructuralRamsey.Partite.Closed.Attachment

open RelStructure Structure

noncomputable section

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

private abbrev maps :
    I → RelStructure.Embedding
      (B.toRelStructure.induce S) D.toRelStructure :=
  fun j => (f j).1.toEmbedding

/-- The chosen-copy part of a closed test is function-closed.

The output is pulled back through the already-closed inclusion of the chosen
attached B-copy.  No closure property of the ambient test T is needed here:
the output vertex is already a vertex of T. -/
theorem piece_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.pieceSet
        B.toRelStructure S D.toRelStructure (maps B S D f) T i) := by
  classical
  let copy : Partite.Closed.Embedding B (RAttach B S D f) :=
    ⟨Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i,
      Partite.Closed.Attachment.copy_closed
        (B := B) (S := S) (D := D) (f := f) hS i⟩
  intro F x y hy hx
  choose a ha using hx
  let args : Fin (L.funcArity F) → V := a
  have hinputs :
      (fun k => (x k).1) = copy ∘ args := by
    funext k
    exact (ha k).symm
  have hyWhole :
      (RAttach B S D f).rel (.inr F)
        (Structure.funcTuple (copy ∘ args) y.1) := by
    change
      (RAttach B S D f).rel (.inr F)
        (Structure.funcTuple (fun k => (x k).1) y.1) at hy
    rwa [hinputs] at hy
  obtain ⟨z, hz, hzy⟩ :=
    copy.toRelClosed.closed F args y.1 hyWhole
  refine ⟨z, ?_⟩
  exact hzy.symm

/-- The rest obtained by deleting the chosen copy's exclusive vertices is
function-closed inside a closed test.

If an output were exclusive to the chosen copy, the attachment relation would
force every input into that copy.  Since the inputs are in the rest, their
preimages must all lie in the closed support S; closure of S then forces the
output preimage into S as well, contradicting exclusivity. -/
theorem rest_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.restSet
        (W := W) (I := I) S T i) := by
  classical
  intro F x y hy hx
  intro hyOutside
  rcases hyOutside with ⟨out, hyEq⟩
  have hyWhole :
      (RAttach B S D f).rel (.inr F)
        (Structure.funcTuple (fun k => (x k).1) y.1) := hy
  have hlast :
      (Structure.funcTuple (fun k => (x k).1) y.1)
          (Fin.last (L.funcArity F)) =
        Sum.inr (i, out) := by
    rw [Structure.funcTuple_last]
    exact hyEq
  obtain ⟨q, hq, heq⟩ :=
    RelStructure.Attachment.relation_eq_copy_of_contains_outside
      (B := B.toRelStructure) (S := S)
      (D := D.toRelStructure) (f := maps B S D f)
      hyWhole (Fin.last (L.funcArity F)) i out hlast
  let args : Fin (L.funcArity F) → V :=
    fun k => q (Fin.castSucc k)
  have hinputCopy :
      ∀ k, (x k).1 =
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure (maps B S D f)
          i (args k) := by
    intro k
    have hk := congrFun heq (Fin.castSucc k)
    rw [Structure.funcTuple_castSucc] at hk
    exact hk
  have hargsS : ∀ k, args k ∈ S := by
    intro k
    by_contra hkS
    apply hx k
    refine ⟨⟨args k, hkS⟩, ?_⟩
    calc
      (x k).1 =
          RelStructure.Attachment.copyMap
            B.toRelStructure S D.toRelStructure (maps B S D f)
            i (args k) := hinputCopy k
      _ = Sum.inr (i, ⟨args k, hkS⟩) :=
        RelStructure.Attachment.copyMap_not_mem
          (B := B.toRelStructure) (S := S)
          (D := D.toRelStructure) (f := maps B S D f)
          i (args k) hkS
  let outB : V := q (Fin.last (L.funcArity F))
  have hrelB :
      B.rel (.inr F) (Structure.funcTuple args outB) := by
    have heta : Structure.funcTuple args outB = q := by
      simpa [args, outB, Language.graph] using
        (Structure.funcTuple_eta (t := q))
    rw [heta]
    exact hq
  have houtS : outB ∈ S := hS F args outB hrelB hargsS
  have hout := congrFun heq (Fin.last (L.funcArity F))
  rw [Structure.funcTuple_last] at hout
  have hyCore :
      y.1 =
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure (maps B S D f)
          i outB := hout
  rw [RelStructure.Attachment.copyMap_mem
      (B := B.toRelStructure) (S := S)
      (D := D.toRelStructure) (f := maps B S D f)
      i outB houtS] at hyCore
  rw [hyEq] at hyCore
  simp at hyCore

/-- The overlap is the intersection of the chosen piece and the rest, hence is
function-closed inside the closed test. -/
theorem overlap_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedSet
      ((RAttach B S D f).toRelStructure.induce T)
      (RelStructure.Attachment.overlapSet
        (W := W) (I := I)
        B.toRelStructure S D.toRelStructure
        (maps B S D f) T i) := by
  intro F x y hy hx
  exact ⟨
    piece_functionClosed B S D f T i hS
      F x y hy (fun k => (hx k).1),
    rest_functionClosed B S D f T i hS
      F x y hy (fun k => (hx k).2)⟩

end

end StructuralRamsey.Partite.Closed.Attachment

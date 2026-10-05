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
  let copyMap :=
    Partite.Attachment.copyEmbedding
      B S D (fun j => (f j).1) i
  have hcopyClosed :
      RelStructure.FunctionClosedMap
        B.toRelStructure
        (RAttach B S D f).toRelStructure copyMap :=
    Partite.Closed.Attachment.copy_closed
      (B := B) (S := S) (D := D) (f := f) hS i
  intro F x y hy hx
  choose a ha using hx
  let args : Fin (L.funcArity F) → V := a
  have hinputs :
      (fun k => (x k).1) = copyMap ∘ args := by
    funext k
    exact ha k
  have hyWhole0 :
      (RAttach B S D f).rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x y) := hy
  have htuple :
      Subtype.val ∘ Structure.funcTuple x y =
        Structure.funcTuple (fun k => (x k).1) y.1 :=
    Structure.comp_funcTuple Subtype.val x y
  have hyWhole :
      (RAttach B S D f).rel (.inr F)
        (Structure.funcTuple (copyMap ∘ args) y.1) := by
    rw [← hinputs, ← htuple]
    exact hyWhole0
  obtain ⟨z, hz, hzy⟩ :=
    hcopyClosed F args y.1 hyWhole
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
  have hyWhole0 :
      (RAttach B S D f).rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x y) := hy
  have htuple :
      Subtype.val ∘ Structure.funcTuple x y =
        Structure.funcTuple (fun k => (x k).1) y.1 :=
    Structure.comp_funcTuple Subtype.val x y
  have hyWhole :
      (RAttach B S D f).rel (.inr F)
        (Structure.funcTuple (fun k => (x k).1) y.1) := by
    rw [← htuple]
    exact hyWhole0
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


/-- The overlap inclusion into the chosen piece is function-closed. -/
theorem overlapToPiece_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedMap
      (RelStructure.Attachment.Overlap
        B.toRelStructure S D.toRelStructure (maps B S D f) T i)
      (RelStructure.Attachment.Piece
        B.toRelStructure S D.toRelStructure (maps B S D f) T i)
      (RelStructure.Attachment.overlapToPiece
        B.toRelStructure S D.toRelStructure (maps B S D f) T i) := by
  let e :=
    RelStructure.Attachment.overlapToPiece
      B.toRelStructure S D.toRelStructure (maps B S D f) T i
  intro F x y hy
  have hySmall0 :
      (RelStructure.Attachment.Small
        B.toRelStructure S D.toRelStructure (maps B S D f) T).rel
        (.inr F)
        (Subtype.val ∘
          Structure.funcTuple (e ∘ x) y) := hy
  have htuple :
      Subtype.val ∘ Structure.funcTuple (e ∘ x) y =
        Structure.funcTuple
          (fun k => (x k).1) y.1 := by
    calc
      Subtype.val ∘ Structure.funcTuple (e ∘ x) y =
          Structure.funcTuple
            (Subtype.val ∘ (e ∘ x)) y.1 :=
        Structure.comp_funcTuple Subtype.val (e ∘ x) y
      _ = Structure.funcTuple (fun k => (x k).1) y.1 := by
        congr 1
  have hySmall :
      (RelStructure.Attachment.Small
        B.toRelStructure S D.toRelStructure (maps B S D f) T).rel
        (.inr F)
        (Structure.funcTuple (fun k => (x k).1) y.1) := by
    rw [← htuple]
    exact hySmall0
  have hyRest :
      y.1 ∈ RelStructure.Attachment.restSet
        (W := W) (I := I) S T i :=
    rest_functionClosed B S D f T i hS
      F (fun k => (x k).1) y.1 hySmall
      (fun k => (x k).2.2)
  let z :
      RelStructure.Attachment.OverlapV
        (W := W) (I := I)
        B.toRelStructure S D.toRelStructure
        (maps B S D f) T i :=
    ⟨y.1, y.2, hyRest⟩
  have hez : e z = y := by
    apply Subtype.ext
    rfl
  refine ⟨z, ?_, hez⟩
  apply
    (e.map_rel_iff
      (show L.graph.Symbol from Sum.inr F)
      (Structure.funcTuple x z)).mp
  have hcomp :
      e ∘ Structure.funcTuple x z =
        Structure.funcTuple (e ∘ x) (e z) :=
    Structure.comp_funcTuple e x z
  have hy' :
      (RelStructure.Attachment.Piece
        B.toRelStructure S D.toRelStructure (maps B S D f) T i).rel
        (show L.graph.Symbol from Sum.inr F)
        (Structure.funcTuple (e ∘ x) (e z)) := by
    simpa [hez] using hy
  exact Eq.mpr
    (congrArg
      (fun t =>
        (RelStructure.Attachment.Piece
          B.toRelStructure S D.toRelStructure (maps B S D f) T i).rel
          (show L.graph.Symbol from Sum.inr F) t)
      hcomp)
    hy'

/-- The overlap inclusion into the complementary rest is function-closed. -/
theorem overlapToRest_functionClosed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedMap
      (RelStructure.Attachment.Overlap
        B.toRelStructure S D.toRelStructure (maps B S D f) T i)
      (RelStructure.Attachment.Rest
        B.toRelStructure S D.toRelStructure (maps B S D f) T i)
      (RelStructure.Attachment.overlapToRest
        B.toRelStructure S D.toRelStructure (maps B S D f) T i) := by
  let e :=
    RelStructure.Attachment.overlapToRest
      B.toRelStructure S D.toRelStructure (maps B S D f) T i
  intro F x y hy
  have hySmall0 :
      (RelStructure.Attachment.Small
        B.toRelStructure S D.toRelStructure (maps B S D f) T).rel
        (.inr F)
        (Subtype.val ∘
          Structure.funcTuple (e ∘ x) y) := hy
  have htuple :
      Subtype.val ∘ Structure.funcTuple (e ∘ x) y =
        Structure.funcTuple
          (fun k => (x k).1) y.1 := by
    calc
      Subtype.val ∘ Structure.funcTuple (e ∘ x) y =
          Structure.funcTuple
            (Subtype.val ∘ (e ∘ x)) y.1 :=
        Structure.comp_funcTuple Subtype.val (e ∘ x) y
      _ = Structure.funcTuple (fun k => (x k).1) y.1 := by
        congr 1
  have hySmall :
      (RelStructure.Attachment.Small
        B.toRelStructure S D.toRelStructure (maps B S D f) T).rel
        (.inr F)
        (Structure.funcTuple (fun k => (x k).1) y.1) := by
    rw [← htuple]
    exact hySmall0
  have hyPiece :
      y.1 ∈ RelStructure.Attachment.pieceSet
        B.toRelStructure S D.toRelStructure (maps B S D f) T i :=
    piece_functionClosed B S D f T i hS
      F (fun k => (x k).1) y.1 hySmall
      (fun k => (x k).2.1)
  let z :
      RelStructure.Attachment.OverlapV
        (W := W) (I := I)
        B.toRelStructure S D.toRelStructure
        (maps B S D f) T i :=
    ⟨y.1, hyPiece, y.2⟩
  have hez : e z = y := by
    apply Subtype.ext
    rfl
  refine ⟨z, ?_, hez⟩
  apply
    (e.map_rel_iff
      (show L.graph.Symbol from Sum.inr F)
      (Structure.funcTuple x z)).mp
  have hcomp :
      e ∘ Structure.funcTuple x z =
        Structure.funcTuple (e ∘ x) (e z) :=
    Structure.comp_funcTuple e x z
  have hy' :
      (RelStructure.Attachment.Rest
        B.toRelStructure S D.toRelStructure (maps B S D f) T i).rel
        (show L.graph.Symbol from Sum.inr F)
        (Structure.funcTuple (e ∘ x) (e z)) := by
    simpa [hez] using hy
  exact Eq.mpr
    (congrArg
      (fun t =>
        (RelStructure.Attachment.Rest
          B.toRelStructure S D.toRelStructure (maps B S D f) T i).rel
          (show L.graph.Symbol from Sum.inr F) t)
      hcomp)
    hy'

/-- The relational decomposition of a closed test decodes to a genuine full
function-language free amalgam.  This is the structural decomposition used in
the mixed functional Picture step. -/
theorem full_decompose
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    let g := maps B S D f
    let hfree :=
      RelStructure.Attachment.decompose
        B.toRelStructure S D.toRelStructure g T i
    let hfPiece :=
      overlapToPiece_functionClosed B S D f T i hS
    let hfRest :=
      overlapToRest_functionClosed B S D f T i hS
    Structure.IsFreeAmalgam
      (⟨RelStructure.Attachment.overlapToPiece
          B.toRelStructure S D.toRelStructure g T i,
        hfPiece⟩ : RelStructure.ClosedEmbedding _ _).toFull
      (⟨RelStructure.Attachment.overlapToRest
          B.toRelStructure S D.toRelStructure g T i,
        hfRest⟩ : RelStructure.ClosedEmbedding _ _).toFull
      (let hs := (hfree.sides_closed_iff).2 ⟨hfPiece, hfRest⟩
       (⟨RelStructure.Attachment.pieceInclusion
          B.toRelStructure S D.toRelStructure g T i,
          hs.1⟩ : RelStructure.ClosedEmbedding _ _).toFull)
      (let hs := (hfree.sides_closed_iff).2 ⟨hfPiece, hfRest⟩
       (⟨RelStructure.Attachment.restInclusion
          B.toRelStructure S D.toRelStructure g T i,
          hs.2⟩ : RelStructure.ClosedEmbedding _ _).toFull) := by
  dsimp
  exact RelStructure.IsFreeAmalgam.toFull
    (RelStructure.Attachment.decompose
      B.toRelStructure S D.toRelStructure
      (maps B S D f) T i)
    (overlapToPiece_functionClosed B S D f T i hS)
    (overlapToRest_functionClosed B S D f T i hS)


/-! Named full-structure view of the closed-test decomposition. -/

abbrev FullSmall :=
  Structure.ofGraph
    (RelStructure.Attachment.Small
      B.toRelStructure S D.toRelStructure (maps B S D f) T)

abbrev FullPiece :=
  Structure.ofGraph
    (RelStructure.Attachment.Piece
      B.toRelStructure S D.toRelStructure (maps B S D f) T i)

abbrev FullRest :=
  Structure.ofGraph
    (RelStructure.Attachment.Rest
      B.toRelStructure S D.toRelStructure (maps B S D f) T i)

abbrev FullOverlap :=
  Structure.ofGraph
    (RelStructure.Attachment.Overlap
      B.toRelStructure S D.toRelStructure (maps B S D f) T i)

noncomputable def fullOverlapToPiece
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    Structure.Embedding
      (FullOverlap B S D f T i)
      (FullPiece B S D f T i) :=
  (⟨RelStructure.Attachment.overlapToPiece
      B.toRelStructure S D.toRelStructure (maps B S D f) T i,
    overlapToPiece_functionClosed B S D f T i hS⟩ :
      RelStructure.ClosedEmbedding _ _).toFull

noncomputable def fullOverlapToRest
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    Structure.Embedding
      (FullOverlap B S D f T i)
      (FullRest B S D f T i) :=
  (⟨RelStructure.Attachment.overlapToRest
      B.toRelStructure S D.toRelStructure (maps B S D f) T i,
    overlapToRest_functionClosed B S D f T i hS⟩ :
      RelStructure.ClosedEmbedding _ _).toFull

noncomputable def fullPieceInclusion
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    Structure.Embedding
      (FullPiece B S D f T i)
      (FullSmall B S D f T) := by
  let hfree :=
    RelStructure.Attachment.decompose
      B.toRelStructure S D.toRelStructure (maps B S D f) T i
  let hfPiece :=
    overlapToPiece_functionClosed B S D f T i hS
  let hfRest :=
    overlapToRest_functionClosed B S D f T i hS
  have hs := (hfree.sides_closed_iff).2 ⟨hfPiece, hfRest⟩
  exact
    (⟨RelStructure.Attachment.pieceInclusion
        B.toRelStructure S D.toRelStructure (maps B S D f) T i,
      hs.1⟩ : RelStructure.ClosedEmbedding _ _).toFull

noncomputable def fullRestInclusion
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    Structure.Embedding
      (FullRest B S D f T i)
      (FullSmall B S D f T) := by
  let hfree :=
    RelStructure.Attachment.decompose
      B.toRelStructure S D.toRelStructure (maps B S D f) T i
  let hfPiece :=
    overlapToPiece_functionClosed B S D f T i hS
  let hfRest :=
    overlapToRest_functionClosed B S D f T i hS
  have hs := (hfree.sides_closed_iff).2 ⟨hfPiece, hfRest⟩
  exact
    (⟨RelStructure.Attachment.restInclusion
        B.toRelStructure S D.toRelStructure (maps B S D f) T i,
      hs.2⟩ : RelStructure.ClosedEmbedding _ _).toFull

theorem full_decompose_named
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    Structure.IsFreeAmalgam
      (fullOverlapToPiece B S D f T i hS)
      (fullOverlapToRest B S D f T i hS)
      (fullPieceInclusion B S D f T i hS)
      (fullRestInclusion B S D f T i hS) := by
  simpa [fullOverlapToPiece, fullOverlapToRest,
    fullPieceInclusion, fullRestInclusion]
    using full_decompose B S D f T i hS


/-- A closed test lying wholly in one attached copy embeds fully back into the
copied functional structure. -/
noncomputable def fullSmallEmbeddingToCopy
    (hSupp : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hTest :
      RelStructure.FunctionClosedSet
        (RAttach B S D f).toRelStructure T)
    (hcopy :
      ∀ z : T,
        RelStructure.Attachment.InCopy
          B.toRelStructure S D.toRelStructure (maps B S D f) i z.1) :
    Structure.Embedding
      (FullSmall B S D f T)
      (Structure.ofGraph B.toRelStructure) := by
  let smallRel :
      RelStructure.ClosedEmbedding
        ((RAttach B S D f).toRelStructure.induce T)
        (RAttach B S D f).toRelStructure :=
    RelStructure.ClosedEmbedding.inclusion
      (RAttach B S D f).toRelStructure T hTest
  let smallFull := smallRel.toFull
  let copyRel :
      RelStructure.ClosedEmbedding
        B.toRelStructure (RAttach B S D f).toRelStructure :=
    ⟨(Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i).toEmbedding,
      Partite.Closed.Attachment.copy_closed
        (B := B) (S := S) (D := D) (f := f) hSupp i⟩
  let copyFull := copyRel.toFull
  have hrange :
      ∀ z : T, ∃ x : V, smallFull z = copyFull x := by
    intro z
    rcases hcopy z with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change z.1 =
      RelStructure.Attachment.copyMap
        B.toRelStructure S D.toRelStructure (maps B S D f) i x
    exact hx
  exact smallFull.factorThroughClosedRange copyFull hrange

/-- A closed test lying wholly in the attachment core embeds fully into the
decoded functional core. -/
noncomputable def fullSmallEmbeddingToCore
    (hSupp : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hTest :
      RelStructure.FunctionClosedSet
        (RAttach B S D f).toRelStructure T)
    (hcore :
      ∀ z : T, ∃ w : W, z.1 =
        Partite.Attachment.coreEmbedding
          B S D (fun j => (f j).1) w) :
    Structure.Embedding
      (FullSmall B S D f T)
      (Structure.ofGraph D.toRelStructure) := by
  let smallRel :
      RelStructure.ClosedEmbedding
        ((RAttach B S D f).toRelStructure.induce T)
        (RAttach B S D f).toRelStructure :=
    ⟨RelStructure.inclusion (RAttach B S D f).toRelStructure T, hTest⟩
  let smallFull := smallRel.toFull
  let coreRel :
      RelStructure.ClosedEmbedding
        D.toRelStructure (RAttach B S D f).toRelStructure :=
    ⟨(Partite.Attachment.coreEmbedding
        B S D (fun j => (f j).1)).toEmbedding,
      Partite.Closed.Attachment.core_closed
        (B := B) (S := S) (D := D) (f := f) hSupp⟩
  let coreFull := coreRel.toFull
  have hrange :
      ∀ z : T, ∃ w : W, smallFull z = coreFull w := by
    intro z
    rcases hcore z with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    change z.1 =
      (Partite.Attachment.coreEmbedding
        B S D (fun j => (f j).1)).toEmbedding w
    exact hw
  exact smallFull.factorThroughClosedRange coreFull hrange

end

end StructuralRamsey.Partite.Closed.Attachment

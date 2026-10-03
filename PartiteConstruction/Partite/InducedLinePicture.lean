import PartiteConstruction.Partite.InducedPicture

/-! # Line-indexed induced pictures

The usual Picture construction attaches a copy of the preceding picture over
*every* partite embedding of the restricted picture into the Hales--Jewett
power.  The Ramsey proof actually uses only the Hales--Jewett line embeddings.

Restricting the attachment indices to lines preserves the Picture Ramsey
property.  Every retained attachment moreover has a parameter coordinate on
which its attaching map is literally the identity.  This extra geometry is
designed for the coherence argument in the iterated construction.
-/
namespace StructuralRamsey.Partite.Induced.LinePicture

open RelStructure HalesJewett SuccessorTree

noncomputable section

universe u v
variable {L : RelLanguage.{u}}
variable {U P X : Type v}

variable (A : RelStructure L U) (D : RelStructure L P)
variable (B : Partite.System L P X)
variable (α : RelStructure.Embedding A D)

private abbrev E (N : ℕ) := Partite.Induced.power (B.restrict α.toFunctionEmbedding) N
private abbrev I (N : ℕ) :=
  Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N

/-- The line embedding re-read as the attaching map on the support of B. -/
def attachingMap
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ) (W : Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N) :
    Partite.Embedding
      (B.induce (B.support α.toFunctionEmbedding))
      ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding) :=
  Partite.Picture.attachingMap B α.toFunctionEmbedding (Partite.Induced.power (B.restrict α.toFunctionEmbedding) N)
    (Partite.Induced.lineEmbedding hR W)

abbrev Vertex
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ) :=
  Partite.Attachment.Vertex
    (B.support α.toFunctionEmbedding)
    (W := Partite.Induced.Vertex (B.restrict α.toFunctionEmbedding) N)
    (I := Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N)

/-- The free attachment using only Hales--Jewett line embeddings. -/
noncomputable def build
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ) :
    Partite.System L P (Vertex (A := A) (D := D) (B := B) (α := α) hR N) :=
  Partite.Attachment.attach
    B (B.support α.toFunctionEmbedding) ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
    (attachingMap (A := A) (D := D) (B := B) (α := α) hR N)

noncomputable def coreEmbedding
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ) :
    Partite.Embedding ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
      (build (A := A) (D := D) (B := B) (α := α) hR N) :=
  Partite.Attachment.coreEmbedding
    B (B.support α.toFunctionEmbedding) ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
    (attachingMap (A := A) (D := D) (B := B) (α := α) hR N)

noncomputable def copyEmbedding
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ)
    (W : Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N) :
    Partite.Embedding B (build (A := A) (D := D) (B := B) (α := α) hR N) :=
  Partite.Attachment.copyEmbedding
    B (B.support α.toFunctionEmbedding) ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
    (attachingMap (A := A) (D := D) (B := B) (α := α) hR N) W

/-- The retained copy indexed by W agrees with the line embedding on the
support. -/
theorem copy_extends
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (N : ℕ)
    (W : Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N) (x : B.support α.toFunctionEmbedding) :
    copyEmbedding (A := A) (D := D) (B := B) (α := α) hR N W x.1 =
      coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
        (attachingMap (A := A) (D := D) (B := B) (α := α) hR N W x) :=
  Partite.Attachment.copy_extends
    B (B.support α.toFunctionEmbedding) ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
    (attachingMap (A := A) (D := D) (B := B) (α := α) hR N) W x

/-- Core copy corresponding to one Hales--Jewett word. -/
def wordCore
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) :
    Partite.ProjectedEmbedding A (build (A := A) (D := D) (B := B) (α := α) hR N) α.toFunctionEmbedding :=
  ⟨(coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N).toEmbedding.comp
      (Partite.Induced.wordEmbedding hR hN w).toEmbedding,
    fun a => by
      change
        (build (A := A) (D := D) (B := B) (α := α) hR N).part
            (coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
              (Partite.Induced.wordEmbedding hR hN w a)) =
          α a
      rw [(coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N).map_part]
      change α ((Partite.Induced.wordEmbedding hR hN w).part _) = α a
      rw [(Partite.Induced.wordEmbedding hR hN w).map_part]⟩

/-- A projected A-copy inside the retained B-copy W is exactly the word-core
copy obtained by substituting its restricted letter into W. -/
theorem copy_comp_restrict
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A) (hN : 0 < N)
    (W : Line (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) N)
    (e : Partite.ProjectedEmbedding A B α.toFunctionEmbedding) :
    e.comp (copyEmbedding (A := A) (D := D) (B := B) (α := α) hR N W) =
      wordCore (A := A) (D := D) (B := B) (α := α) hR hN
        (W.eval (Partite.Picture.restrictEmbedding e)) := by
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro a
  change
    copyEmbedding (A := A) (D := D) (B := B) (α := α) hR N W (e.val a) =
      coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
        (Partite.Induced.wordEmbedding hR hN
          (W.eval (Partite.Picture.restrictEmbedding e)) a)
  let x : B.support α.toFunctionEmbedding :=
    ⟨e.val a, a, (e.property a).symm⟩
  calc
    copyEmbedding (A := A) (D := D) (B := B) (α := α) hR N W (e.val a) =
        coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
          (attachingMap (A := A) (D := D) (B := B) (α := α) hR N W x) :=
      copy_extends (A := A) (D := D) (B := B) (α := α) hR N W x
    _ = coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
          ((Partite.Induced.lineEmbedding hR W)
            (Partite.Picture.restrictEmbedding e a)) := rfl
    _ = coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N
          (Partite.Induced.wordEmbedding hR hN
            (W.eval (Partite.Picture.restrictEmbedding e)) a) := by
      apply congrArg (coreEmbedding (A := A) (D := D) (B := B) (α := α) hR N)
      exact congrArg
        (fun q : Partite.Embedding
            (Partite.transversal A) (Partite.Induced.power (B.restrict α.toFunctionEmbedding) N) => q a)
        (Partite.Induced.lineEmbedding_comp_letter hR hN W
          (Partite.Picture.restrictEmbedding e))

/-- The line-indexed attachment has the same Picture Ramsey property as the
usual all-embedding attachment. -/
theorem property
    [Finite U] [Finite X]
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A)
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, ∃ hN : 0 < N,
      Partite.PictureProperty A B α.toFunctionEmbedding
        (build (A := A) (D := D) (B := B) (α := α) hR N) κ := by
  classical
  letI : Fintype (Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) :=
    Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite
      (α := Partite.Induced.Letter A (B.restrict α.toFunctionEmbedding)) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordCore (A := A) (D := D) (B := B) (α := α) hR hN w))
  refine ⟨copyEmbedding (A := A) (D := D) (B := B) (α := α) hR N W, ?_⟩
  intro e₁ e₂
  rw [copy_comp_restrict (A := A) (D := D) (B := B) (α := α) hR hN W e₁,
      copy_comp_restrict (A := A) (D := D) (B := B) (α := α) hR hN W e₂]
  exact hW
    (Partite.Picture.restrictEmbedding e₁)
    (Partite.Picture.restrictEmbedding e₂)

/-- The line-indexed picture remains D-partite. -/
theorem isPartiteOver
    (hB : B.IsPartiteOver D)
    (hR : (B.restrict α.toFunctionEmbedding).IsPartiteOver A)
    (N : ℕ) (hN : 0 < N) :
    (build (A := A) (D := D) (B := B) (α := α) hR N).IsPartiteOver D := by
  have hE : (Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  have hCore :
      ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := Partite.Induced.power (B.restrict α.toFunctionEmbedding) N) hE α
  exact Partite.Attachment.attach_isPartiteOver
    B (B.support α.toFunctionEmbedding) ((Partite.Induced.power (B.restrict α.toFunctionEmbedding) N).relabel α.toFunctionEmbedding)
    (attachingMap (A := A) (D := D) (B := B) (α := α) hR N) hB hCore

end StructuralRamsey.Partite.Induced.LinePicture

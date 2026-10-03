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

universe u v
variable {L : RelLanguage.{u}}
variable {U P X : Type v}

variable (A : RelStructure L U) (D : RelStructure L P)
variable (B : Partite.System L P X)
variable (α : RelStructure.Embedding A D)

private abbrev αf := α.toFunctionEmbedding
private abbrev R := B.restrict α.toFunctionEmbedding
private abbrev E (N : ℕ) := Partite.Induced.power (R B α) N
private abbrev I (N : ℕ) :=
  Line (Partite.Induced.Letter A (R B α)) N

/-- The line embedding re-read as the attaching map on the support of B. -/
def attachingMap
    (hR : (R B α).IsPartiteOver A) (N : ℕ) (W : I A B α N) :
    Partite.Embedding
      (B.induce (B.support (αf α)))
      ((E A B α N).relabel (αf α)) :=
  Partite.Picture.attachingMap B (αf α) (E A B α N)
    (Partite.Induced.lineEmbedding hR W)

abbrev Vertex
    (hR : (R B α).IsPartiteOver A) (N : ℕ) :=
  Partite.Attachment.Vertex
    (B.support (αf α))
    (W := Partite.Induced.Vertex (R B α) N)
    (I := I A B α N)

/-- The free attachment using only Hales--Jewett line embeddings. -/
noncomputable def build
    (hR : (R B α).IsPartiteOver A) (N : ℕ) :
    Partite.System L P (Vertex A B α hR N) :=
  Partite.Attachment.attach
    B (B.support (αf α)) ((E A B α N).relabel (αf α))
    (attachingMap A B α hR N)

noncomputable def coreEmbedding
    (hR : (R B α).IsPartiteOver A) (N : ℕ) :
    Partite.Embedding ((E A B α N).relabel (αf α))
      (build A B α hR N) :=
  Partite.Attachment.coreEmbedding
    B (B.support (αf α)) ((E A B α N).relabel (αf α))
    (attachingMap A B α hR N)

noncomputable def copyEmbedding
    (hR : (R B α).IsPartiteOver A) (N : ℕ)
    (W : I A B α N) :
    Partite.Embedding B (build A B α hR N) :=
  Partite.Attachment.copyEmbedding
    B (B.support (αf α)) ((E A B α N).relabel (αf α))
    (attachingMap A B α hR N) W

/-- The retained copy indexed by W agrees with the line embedding on the
support. -/
theorem copy_extends
    (hR : (R B α).IsPartiteOver A) (N : ℕ)
    (W : I A B α N) (x : B.support (αf α)) :
    copyEmbedding A B α hR N W x.1 =
      coreEmbedding A B α hR N
        (attachingMap A B α hR N W x) :=
  Partite.Attachment.copy_extends
    B (B.support (αf α)) ((E A B α N).relabel (αf α))
    (attachingMap A B α hR N) W x

/-- Core copy corresponding to one Hales--Jewett word. -/
def wordCore
    (hR : (R B α).IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Partite.Induced.Letter A (R B α)) :
    Partite.ProjectedEmbedding A (build A B α hR N) (αf α) :=
  ⟨(coreEmbedding A B α hR N).toEmbedding.comp
      (Partite.Induced.wordEmbedding hR hN w).toEmbedding,
    fun a => by
      change
        (build A B α hR N).part
            (coreEmbedding A B α hR N
              (Partite.Induced.wordEmbedding hR hN w a)) =
          α a
      rw [(coreEmbedding A B α hR N).map_part]
      change α ((Partite.Induced.wordEmbedding hR hN w).part _) = α a
      rw [(Partite.Induced.wordEmbedding hR hN w).map_part]⟩

/-- A projected A-copy inside the retained B-copy W is exactly the word-core
copy obtained by substituting its restricted letter into W. -/
theorem copy_comp_restrict
    (hR : (R B α).IsPartiteOver A) (hN : 0 < N)
    (W : I A B α N)
    (e : Partite.ProjectedEmbedding A B (αf α)) :
    e.comp (copyEmbedding A B α hR N W) =
      wordCore A B α hR hN
        (W.eval (Partite.Picture.restrictEmbedding e)) := by
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro a
  change
    copyEmbedding A B α hR N W (e.val a) =
      coreEmbedding A B α hR N
        (Partite.Induced.wordEmbedding hR hN
          (W.eval (Partite.Picture.restrictEmbedding e)) a)
  let x : B.support (αf α) :=
    ⟨e.val a, a, (e.property a).symm⟩
  calc
    copyEmbedding A B α hR N W (e.val a) =
        coreEmbedding A B α hR N
          (attachingMap A B α hR N W x) :=
      copy_extends A B α hR N W x
    _ = coreEmbedding A B α hR N
          ((Partite.Induced.lineEmbedding hR W)
            (Partite.Picture.restrictEmbedding e a)) := rfl
    _ = coreEmbedding A B α hR N
          (Partite.Induced.wordEmbedding hR hN
            (W.eval (Partite.Picture.restrictEmbedding e)) a) := by
      apply congrArg (coreEmbedding A B α hR N)
      exact congrArg
        (fun q : Partite.Embedding
            (Partite.transversal A) (E A B α N) => q a)
        (Partite.Induced.lineEmbedding_comp_letter hR hN W
          (Partite.Picture.restrictEmbedding e))

/-- The line-indexed attachment has the same Picture Ramsey property as the
usual all-embedding attachment. -/
theorem property
    [Finite U] [Finite X]
    (hR : (R B α).IsPartiteOver A)
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, ∃ hN : 0 < N,
      Partite.PictureProperty A B (αf α)
        (build A B α hR N) κ := by
  classical
  letI : Fintype (Partite.Induced.Letter A (R B α)) :=
    Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite
      (α := Partite.Induced.Letter A (R B α)) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordCore A B α hR hN w))
  refine ⟨copyEmbedding A B α hR N W, ?_⟩
  intro e₁ e₂
  rw [copy_comp_restrict A B α hR hN W e₁,
      copy_comp_restrict A B α hR hN W e₂]
  exact hW
    (Partite.Picture.restrictEmbedding e₁)
    (Partite.Picture.restrictEmbedding e₂)

/-- The line-indexed picture remains D-partite. -/
theorem isPartiteOver
    (hB : B.IsPartiteOver D)
    (hR : (R B α).IsPartiteOver A)
    (N : ℕ) (hN : 0 < N) :
    (build A B α hR N).IsPartiteOver D := by
  have hE : (E A B α N).IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  have hCore :
      ((E A B α N).relabel (αf α)).IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E A B α N) hE α
  exact Partite.Attachment.attach_isPartiteOver
    B (B.support (αf α)) ((E A B α N).relabel (αf α))
    (attachingMap A B α hR N) hB hCore

end StructuralRamsey.Partite.Induced.LinePicture

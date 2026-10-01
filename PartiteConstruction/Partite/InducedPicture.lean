import PartiteConstruction.Partite.InducedAttachment
import PartiteConstruction.Partite.Picture

/-! # The induced Picture Lemma

Restrict to the parts selected by an embedding of the source into the part
structure, use the coordinatewise induced Partite Lemma, relabel the resulting
core back into the ambient part structure, and freely attach full copies.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {U : Type w} {V : Type z}
variable (A : RelStructure L U) (D : RelStructure L P)
variable (B : System L P V) (α : RelStructure.Embedding A D)

/-- Relational induced Picture Lemma. The witness is definitionally a free
attachment over a positive coordinatewise power, so it has exactly the
"based" form used in Appendix A. -/
theorem pictureLemma (hB : B.IsPartiteOver D)
    [Finite U] [Finite V] (κ : Type*) [Fintype κ] :
    ∃ (W : Type (max w z)) (_ : Finite W) (C : System L P W),
      C.IsPartiteOver D ∧ PictureProperty A B α.toFunctionEmbedding C κ := by
  classical
  let αf : U ↪ P := α.toFunctionEmbedding
  let R := B.restrict αf
  have hR : R.IsPartiteOver A :=
    restrict_isPartiteOver D B A hB α
  obtain ⟨N, hN, hArrow⟩ := partiteLemma (A := A) (B := R) hR κ
  let E := power R N
  have hE : E.IsPartiteOver A := power_isPartiteOver hR hN
  have hCore : (E.relabel αf).IsPartiteOver D :=
    relabel_isPartiteOver (A := A) (B := E) hE α
  let C := Picture.build B αf E
  have hC : C.IsPartiteOver D := by
    exact Attachment.attach_isPartiteOver B (B.support αf) (E.relabel αf)
      (Picture.attachingMap B αf E) hB hCore
  exact ⟨Picture.Vertex B αf E, inferInstance, C, hC,
    Picture.property B αf E κ hArrow⟩

end StructuralRamsey.Partite.Induced

import PartiteConstruction.Partite.Attachment
import PartiteConstruction.Partite.NonInduced
import PartiteConstruction.Partite.Projection

/-! # The non-induced Picture Lemma

Restrict to the parts selected by an injective projection, apply the Partite
Lemma there, and attach a full copy over every embedding of the restriction.
The core and all attached copies are induced relational substructures.
-/
namespace StructuralRamsey.Partite

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v} {U : Type w} {V : Type z}
variable (A : RelStructure L U) (B : System L P V) (α : U ↪ P)

/-- The local conclusion used at each step of the construction. -/
def PictureProperty {W : Type*} (C : System L P W) (κ : Type*) : Prop :=
  ∀ χ : ProjectedEmbedding A C α → κ,
    ∃ f : Embedding B C, ∀ e₁ e₂ : ProjectedEmbedding A B α,
      χ (e₁.comp f) = χ (e₂.comp f)

namespace Picture

variable {A B α}

def restrictEmbedding (e : ProjectedEmbedding A B α) :
    Embedding (transversal A) (B.restrict α) where
  toFun x := ⟨e.val x, x, (e.property x).symm⟩
  injective _ _ h := e.val.injective (congrArg Subtype.val h)
  map_rel_iff R x := e.val.map_rel_iff R x
  map_part x := α.injective ((B.restrictedPart_spec α _).trans (e.property x))

variable (B α) {W : Type t} (D : System L U W)

def attachingMap (f : Embedding (B.restrict α) D) :
    Embedding (B.induce (B.support α)) (D.relabel α) where
  toEmbedding := f.toEmbedding
  map_part x := (congrArg α (f.map_part x)).trans (B.restrictedPart_spec α x)

abbrev Vertex := Attachment.Vertex (B.support α) (W := W)
  (I := Embedding (B.restrict α) D)

noncomputable def build : System L P (Vertex B α D) :=
  Attachment.attach B (B.support α) (D.relabel α) (attachingMap B α D)

noncomputable def coreEmbedding : Embedding (D.relabel α) (build B α D) :=
  Attachment.coreEmbedding B (B.support α) (D.relabel α) (attachingMap B α D)

noncomputable def copyEmbedding (f : Embedding (B.restrict α) D) :
    Embedding B (build B α D) :=
  Attachment.copyEmbedding B (B.support α) (D.relabel α) (attachingMap B α D) f

noncomputable def coreLetter (e : Embedding (transversal A) D) :
    ProjectedEmbedding A (build B α D) α :=
  ⟨(coreEmbedding B α D).toEmbedding.comp e.toEmbedding, fun x =>
    ((coreEmbedding B α D).map_part (e x)).trans (congrArg α (e.map_part x))⟩

theorem copy_comp_restrict (f : Embedding (B.restrict α) D)
    (e : ProjectedEmbedding A B α) :
    e.comp (copyEmbedding B α D f) = coreLetter B α D (f.comp (restrictEmbedding e)) := by
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro x
  exact Attachment.copy_extends B (B.support α) (D.relabel α) (attachingMap B α D)
    f ⟨e.val x, x, (e.property x).symm⟩

theorem property (κ : Type*) (hD : Arrow (transversal A) (B.restrict α) D κ) :
    PictureProperty A B α (build B α D) κ := by
  intro χ
  obtain ⟨f, hf⟩ := hD (fun e => χ (coreLetter B α D e))
  refine ⟨copyEmbedding B α D f, ?_⟩
  intro e₁ e₂
  rw [copy_comp_restrict, copy_comp_restrict]
  exact hf (restrictEmbedding e₁) (restrictEmbedding e₂)

end Picture

/-- Appendix A's Picture Lemma, with an explicitly finite witness and no
assumption of occupied parts, positive relation arities, or nonempty colours. -/
theorem pictureLemma [Finite U] [Finite V] (κ : Type*) [Fintype κ] :
    ∃ (W : Type (max w z)) (_ : Finite W) (C : System L P W),
      PictureProperty A B α C κ := by
  classical
  obtain ⟨N, _, hN⟩ := NonInduced.partiteLemma (A := A) (B := B.restrict α) κ
  let D := NonInduced.power A (B.restrict α) N
  exact ⟨Picture.Vertex B α D, inferInstance, Picture.build B α D,
    Picture.property B α D κ hN⟩

end StructuralRamsey.Partite

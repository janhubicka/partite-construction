import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019
import PartiteConstruction.Ramsey.Basic

/-!
# Ramsey arrows lift and descend along canonical full-root tagging

This is the same purely relational functorial step used in the
verified 2019 generated-profile / second closed-Picture proof.
Canonical whole-mask full-root tags use the SAME vertex carrier.

A full OLD complete-mask embedding lifts to a full embedding of its
canonical tagged structures. A full tagged embedding forgets to
the OLD structure. The two conversions preserve underlying maps
and composition, which is enough to lift an OLD Ramsey arrow to the
tagged language and to recover an OLD Ramsey arrow from an arbitrary
tagged Ramsey target.

The latter direction does NOT assume the target's fresh tags are
canonical. Thus the second U-closed tagged pass can return to the
OLD language without a false intermediate target-normality premise.
No weak substructure is closed or enlarged here.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V W X : Type w}

/-- A Ramsey arrow for OLD complete function-mask structures lifts to
canonical full-root tagged copies by functoriality of full embeddings.
The source and target vertex carriers are unchanged. -/
theorem wholeMaskTag_arrow
    (A : RelStructure (L.wholeMaskPatternLanguage P) V)
    (B : RelStructure (L.wholeMaskPatternLanguage P) W)
    (C : RelStructure (L.wholeMaskPatternLanguage P) X)
    (κ : Type*) (h : StructuralRamsey.Arrow A B C κ) :
    StructuralRamsey.Arrow
      (wholeMaskTagExpansion A) (wholeMaskTagExpansion B)
      (wholeMaskTagExpansion C) κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun a => χ a.wholeMaskTag)
  refine ⟨f.wholeMaskTag, ?_⟩
  intro a₁ a₂
  have hComp (a : Embedding (wholeMaskTagExpansion A)
      (wholeMaskTagExpansion B)) :
      f.wholeMaskTag.comp a =
        (f.comp a.wholeMaskTagReduct).wholeMaskTag := by
    apply Embedding.ext
    intro x
    rfl
  calc
    χ (f.wholeMaskTag.comp a₁) =
        χ ((f.comp a₁.wholeMaskTagReduct).wholeMaskTag) :=
      congrArg χ (hComp a₁)
    _ = χ ((f.comp a₂.wholeMaskTagReduct).wholeMaskTag) :=
      hf a₁.wholeMaskTagReduct a₂.wholeMaskTagReduct
    _ = χ (f.wholeMaskTag.comp a₂) :=
      congrArg χ (hComp a₂).symm

/-- Conversely, ANY tagged Ramsey target yields a Ramsey arrow in its
OLD reduct. Only canonical tags on A and B are needed; the target
itself need NOT be canonical or functionally normalized. -/
theorem wholeMaskTag_forget_arrow
    (A : RelStructure (L.wholeMaskPatternLanguage P) V)
    (B : RelStructure (L.wholeMaskPatternLanguage P) W)
    (C : RelStructure (L.wholeMaskTagLanguage P) X)
    (κ : Type*)
    (h : StructuralRamsey.Arrow
      (wholeMaskTagExpansion A) (wholeMaskTagExpansion B) C κ) :
    StructuralRamsey.Arrow A B (wholeMaskTagReduct C) κ := by
  intro χ
  obtain ⟨f, hf⟩ := h (fun a => χ a.wholeMaskTagReduct)
  refine ⟨f.wholeMaskTagReduct, ?_⟩
  intro a₁ a₂
  have hComp (a : Embedding A B) :
      f.wholeMaskTagReduct.comp a =
        (f.comp a.wholeMaskTag).wholeMaskTagReduct := by
    apply Embedding.ext
    intro x
    rfl
  calc
    χ (f.wholeMaskTagReduct.comp a₁) =
        χ ((f.comp a₁.wholeMaskTag).wholeMaskTagReduct) :=
      congrArg χ (hComp a₁)
    _ = χ ((f.comp a₂.wholeMaskTag).wholeMaskTagReduct) :=
      hf a₁.wholeMaskTag a₂.wholeMaskTag
    _ = χ (f.wholeMaskTagReduct.comp a₂) :=
      congrArg χ (hComp a₂).symm

end StructuralRamsey.RelStructure

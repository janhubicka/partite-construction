import PartiteConstruction.Partite.InducedBased
import PartiteConstruction.Partite.InducedInvariant

/-! # One induced construction step

This combines the induced Partite Lemma, the canonical free attachment, the
homomorphism-embedding projection invariant, the irreducible-image invariant,
and the formal `BasedOn` witness.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X : Type v}

theorem pictureStep
    (A : RelStructure L U) (B₀ : RelStructure L V) (D₀ : RelStructure L P)
    (C₀ : System L P X) (α : RelevantEmbedding A B₀ D₀)
    [Finite U] [Finite X] (κ : Type*) [Fintype κ]
    (hPartite : C₀.IsPartiteOver D₀)
    (hCover : CoversIrreduciblesBy C₀ B₀ D₀) :
    ∃ (Y : Type v) (_ : Finite Y) (C₁ : System L P Y),
      C₁.IsPartiteOver D₀ ∧
      CoversIrreduciblesBy C₁ B₀ D₀ ∧
      BasedOn A D₀ C₀ α.1 C₁ ∧
      PictureProperty A C₀ α.1.toFunctionEmbedding C₁ κ := by
  classical
  let αf : U ↪ P := α.1.toFunctionEmbedding
  let R := C₀.restrict αf
  have hR : R.IsPartiteOver A :=
    restrict_isPartiteOver D₀ C₀ A hPartite α.1
  obtain ⟨N, hN, hArrow⟩ := partiteLemma (A := A) (B := R) hR κ
  let E := power R N
  have hE : E.IsPartiteOver A := power_isPartiteOver hR hN
  have hCorePartite : (E.relabel αf).IsPartiteOver D₀ :=
    relabel_isPartiteOver (A := A) (B := E) hE α.1
  let C₁ := Picture.build C₀ αf E
  have hC₁Partite : C₁.IsPartiteOver D₀ := by
    exact Partite.Attachment.attach_isPartiteOver
      C₀ (C₀.support αf) (E.relabel αf)
      (Picture.attachingMap C₀ αf E) hPartite hCorePartite
  have hCoreCover : CoversIrreduciblesBy (E.relabel αf) B₀ D₀ :=
    relabel_covers_of_relevant A B₀ D₀ E α
  have hC₁Cover : CoversIrreduciblesBy C₁ B₀ D₀ := by
    exact Attachment.attach_covers B₀ D₀
      C₀ (C₀.support αf) (E.relabel αf)
      (Picture.attachingMap C₀ αf E) hCover hCoreCover
  have hBased : BasedOn A D₀ C₀ α.1 C₁ := by
    exact canonical_based (A := A) (D := D₀) (B := C₀) (α := α.1) N hN
  have hPicture : PictureProperty A C₀ αf C₁ κ :=
    Picture.property C₀ αf E κ hArrow
  exact ⟨Picture.Vertex C₀ αf E, inferInstance, C₁,
    hC₁Partite, hC₁Cover, hBased, hPicture⟩

end StructuralRamsey.Partite.Induced

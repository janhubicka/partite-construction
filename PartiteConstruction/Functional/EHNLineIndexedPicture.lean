import PartiteConstruction.Functional.EHNLineOnlyPicture

/-!
# Compatibility names for the Hales-Jewett line-indexed functional Picture

The reusable strengthening is
`pictureLemma_lines_preservingSupport`, which also carries an arbitrary
stage invariant through the actual genuine set-valued-function core and
binary attachments. The bare line-indexed Picture theorem is a short
specialization of it, not a second independent Hales-Jewett proof.

Both versions attach only along actual HJ LINES, while retaining all
full functional embeddings, each per-fibre TRANSVERSAL output image,
and the ordinary EHN PictureProperty. The maximal mixed local-tree
invariant across distinct line attachments remains unproved.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P U : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The finite line family is already an instance from
`EHNLineOnlyPicture.finiteLines`; this name is retained for callers. -/
theorem finite_HJLines
    {α : Type v} [Finite α] (N : ℕ) :
    Finite (Line α N) := inferInstance

/-- Bare native functional line-indexed Picture Ramsey lemma.
The stronger `pictureLemma_lines_preservingSupport` proves this while
preserving an auxiliary stage predicate, so no proof replay occurs. -/
theorem pictureLemma_lineIndexed
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D, PictureProperty A B C α κ :=
  pictureLemma_lines hK A hA B α κ

end StructuralRamsey.FunctionalPartite.EHN

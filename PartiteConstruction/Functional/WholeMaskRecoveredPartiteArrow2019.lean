import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Recover a true partial-function Ramsey arrow from a relational witness

The verified 2019 two-pass generated-profile sparsening first constructs
a RELATIONAL Ramsey witness. We need the LAST categorical transfer:
a full relational embedding of canonical part-labelled OLD complete-mask
A or B into that final target must give a full, part-preserving
Option(Set) function embedding ON THE SAME VERTEX MAP.

If these two copywise recovery maps have been proved (by protected
closed U-irreducible B-copy coverage and the final decoder), then
the original relational Ramsey arrow directly implies a genuine
part-preserving partial-function Ramsey arrow. The proof uses
only the naturality of full OLD encoding, the strict equality of
underlying vertex maps and composition of the functional embeddings.

This makes the last transfer obligation precise. It does NOT assume
an arbitrary intermediate tagged picture is already functional,
nor ask for strict native B-trees on intermediate mixed roots.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

/-- The RELATIONAL Ramsey arrow from the verified 2019 profile route
implies the TRUE functional partite Ramsey arrow when each full
canonical OLD A- and B-copy in the FINAL target admits a full
part-preserving partial-function interpretation on the SAME vertices.

No conversion is required for arbitrary intermediate diagrams.
No inverse construction of every functional A-copy of the final
target as an OLD relation embedding is required either: one only
needs to encode A-copies of the selected B-witness. -/
theorem partPreservingArrow_of_relational_old_covered
    (A : PartialSetStructure L V) (partA : V → P)
    (B : PartialSetStructure L W) (partB : W → P)
    (D : PartialSetStructure L X) (partD : X → P)
    (Old : RelStructure ((L.withParts P).wholeMaskPatternLanguage P) X)
    (κ : Type*)
    (hRelArrow : StructuralRamsey.Arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      Old κ)
    (recoverA : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) Old →
      PartPreservingEmbedding A partA D partD)
    (recoverB : RelStructure.Embedding
      (withPartsWholeMaskOld B partB) Old →
      PartPreservingEmbedding B partB D partD)
    (hA : ∀ (e : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) Old) (x : V),
      (recoverA e).1.toFun x = e x)
    (hB : ∀ (e : RelStructure.Embedding
      (withPartsWholeMaskOld B partB) Old) (x : W),
      (recoverB e).1.toFun x = e x) :
    PartPreservingArrow A partA B partB D partD κ := by
  intro χ
  obtain ⟨f,hf⟩ := hRelArrow (fun e => χ (recoverA e))
  refine ⟨recoverB f, ?_⟩
  intro a₁ a₂
  have hNaturality (a : PartPreservingEmbedding A partA B partB) :
      recoverA (f.comp a.encode) =
        (recoverB f).comp a := by
    apply Subtype.ext
    apply PartialSetStructure.Embedding.ext
    intro x
    change (recoverA (f.comp a.encode)).1.toFun x =
      (recoverB f).1.toFun (a.1.toFun x)
    rw [hA (f.comp a.encode) x, hB f (a.1.toFun x)]
    rfl
  rw [← hNaturality a₁, ← hNaturality a₂]
  exact hf a₁.encode a₂.encode

end StructuralRamsey.PartialSetStructure

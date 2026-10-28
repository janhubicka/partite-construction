import PartiteConstruction.Functional.WholeMaskCoveredOutputPartSoundness2019
import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019
import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019

/-!
# The final 2019 protected tagged target is genuinely partial and partite

The verified two-pass profile sparsening theorem constructs a FINAL
U-closed relational Picture with protected canonical B-copy coverage.
Only then do we decode its OLD complete-mask value/domain relations
into genuine Option(Set)-valued functions, preserving none vs some-empty.

The source language was expanded by unary part predicates BEFORE the
OLD full-mask encoding. Protected closed U-irreducible B-copy coverage
forces each final target vertex to have exactly one part predicate,
including isolated vertices. It also forces every old complete
output-value relation to use those exact vertex parts.

This module forgets the unary predicates from the decoded function
language and interprets every full OLD canonical source copy as a
genuine FULL part-preserving partial-function embedding into the
decoded final target, with the IDENTICAL underlying map. These
are precisely the copywise recovery maps needed for the final
relational-to-functional Ramsey-arrow transfer.

There is no false native mixed-root strict B-tree completion premise,
no requirement that intermediate profiles already decode, and no
enlargement of original weak tests or their projected images.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

/-- Forget only the unary *source part* predicates from the
genuinely partial Option(Set) decoder of a tagged relational
target. Every partial function value (including some empty)
is retained literally. -/
def wholeMaskOriginalDecode
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W) :
    PartialSetStructure L W where
  rel R xs :=
    ((wholeMaskTagReduct C).wholeMaskPartialDecode).rel
      (.inl (ULift.up R)) xs
  func F xs :=
    ((wholeMaskTagReduct C).wholeMaskPartialDecode).func
      (ULift.up F) xs

/-- The exact final target's decoded ORIGINAL partial functions
are transversal to its recovered unary part map. Both part
normality and output label compatibility are now DERIVED from
the same U-closed protected canonical B-copy coverage. -/
theorem wholeMaskOriginalDecode_fibreTransversal_of_covered
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L X) (basePart : X → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) :
    FibreTransversal (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C Base basePart hC hCover) := by
  have hTrans := wholeMaskCoveredPart_decoder_fibreTransversal
    C Base basePart hC hPos hCover
  intro F xs U hv y hy z hz hPart
  exact hTrans (ULift.up F) xs U hv y hy z hz hPart

namespace Embedding

/-- A FULL OLD unary-part-labelled complete-mask relational copy of
finite genuinely partial A inside a FINAL closed B-covered tagged
Picture is already a FULL genuine partial-function copy on the
SAME vertices, preserving its actual recovered target part labels.

In particular a missing source function domain stays missing;
the map is stronger than the global original-2019 partial projection. -/
noncomputable def ofCoveredPartiteWholeMaskOld
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L X) (basePart : X → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) (wholeMaskTagReduct C)) :
    PartPreservingEmbedding A partA (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C Base basePart hC hCover) := by
  classical
  let Aplus := A.withParts partA
  have hTransPlus : FibreTransversal Aplus partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTransA
  let g : Embedding Aplus
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) :=
    Embedding.ofCoveredWholeMaskPatternGraph
      Aplus partA hTransPlus C (Base.withParts basePart)
      basePart hC (hPos.withParts) hCover f
  let original : Embedding A (wholeMaskOriginalDecode C) := {
    toFun := g.toFun
    injective := g.injective
    map_rel_iff := by
      intro R xs
      exact g.map_rel_iff (.inl (ULift.up R)) xs
    map_func := by
      intro F xs
      exact g.map_func (ULift.up F) xs
  }
  refine ⟨original, ?_⟩
  intro x
  have hUnary : WholeMaskVertexPartHolds C (g.toFun x) (partA x) := by
    have h := (g.map_rel_iff (.inr (partA x))
      (fun _ : Fin 1 => x)).mpr
      (show Aplus.rel (.inr (partA x))
        (fun _ : Fin 1 => x) from rfl)
    exact h
  have hUnique :=
    (Classical.choose_spec
      (wholeMask_vertexPart_existsUnique_of_closed_coverage
        C Base basePart hC hCover (g.toFun x))).2
  exact (hUnique (partA x) hUnary).symm

/-- The decoded full genuine partial-function copy has the
LITERAL OLD relational embedding as its underlying vertex map. -/
theorem ofCoveredPartiteWholeMaskOld_apply
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L X) (basePart : X → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) (wholeMaskTagReduct C))
    (x : V) :
    ((Embedding.ofCoveredPartiteWholeMaskOld
      A partA hTransA C Base basePart hC hPos hCover f).1.toFun x) =
      f x := by
  rfl

end Embedding
end StructuralRamsey.PartialSetStructure

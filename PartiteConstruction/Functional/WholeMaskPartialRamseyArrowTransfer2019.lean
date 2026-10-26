import PartiteConstruction.Structure.PartialSetFunctionsEmbeddingComposition
import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019
import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019
import PartiteConstruction.Functional.WholeMaskTagArrow2019

/-!
# From the 2019 complete-mask relational Ramsey arrow to genuine functions

The verified 2019 generated-profile proof yields a relational
Ramsey arrow. Full OLD complete-mask embeddings of its finite
canonical genuine-partial sources decode to FULL genuine partial
function embeddings of the final target; conversely, a FULL
part-preserving source embedding A→B lifts to a FULL OLD embedding.
These translations compose on the SAME vertex map.

Thus the relational arrow implies genuine functional monochromaticity
for exactly the A-copies of B that preserve their chosen part labels,
without assuming the target intermediate pictures themselves decode
to functional structures. The target only needs complete-value
uniqueness and exact domain decoding, already certified under the
final protected closed B-copy coverage hypothesis.

The distinction matters: the raw complete-mask graph alone does not
name the part of isolated vertices, so it would be unsound to claim
that *every* arbitrary functional A→B embedding necessarily
preserves the specified part map. Unary part predicates (already
available in ClosurePartPredicates) are used for the unrestricted
partite-embedding interpretation in the subsequent step.

The construction remains independent of any native maximal-mixed
strict FUNCTIONAL B-tree completion at intermediate stages.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {U V W Q : Type w}

/-- The functional Ramsey-arrow conclusion for the specified
PART-PRESERVING A-copies of B. The final B embedding need not
preserve any extra external part map on C, whose true functional
structure is decoded only at the end. -/
def PartPreservingArrow
    (A : PartialSetStructure L U) (B : PartialSetStructure L V)
    (C : PartialSetStructure L W)
    (partA : U → P) (partB : V → P) (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ,
    ∃ β : Embedding B C,
      ∀ (α₁ α₂ : Embedding A B),
        (∀ x, partB (α₁.toFun x) = partA x) →
        (∀ x, partB (α₂.toFun x) = partA x) →
        χ (β.comp α₁) = χ (β.comp α₂)

/-- Any old complete-mask RELATIONAL arrow, into a target with
unique complete values and exact OLD-domain decoding, transfers
to full genuinely partial Option(Set) functions, monochromatic
on every role-preserving A-copy of B.

Both source and target full embeddings are decoded literally on
the original vertex maps; the proof does not close weak tests. -/
theorem PartPreservingArrow.ofWholeMaskRelationalArrow
    (A : PartialSetStructure L U) [Finite U]
    (B : PartialSetStructure L V) [Finite V]
    (partA : U → P) (partB : V → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (E : RelStructure (L.wholeMaskPatternLanguage P) W)
    (hUnique : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W) (S T : Set W),
      HasWholeMaskValue E F xs S →
      HasWholeMaskValue E F xs T → S = T)
    (hDomain : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W),
      E.wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain E F xs)
    (κ : Type*) (hArrow : StructuralRamsey.Arrow
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) E κ) :
    PartPreservingArrow A B E.wholeMaskPartialDecode
      partA partB κ := by
  classical
  let decodeA (f : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA) E) :
      Embedding A E.wholeMaskPartialDecode :=
    Embedding.ofWholeMaskPatternGraph A partA hTransA E
      hUnique hDomain f
  let decodeB (f : RelStructure.Embedding
      (B.wholeMaskPatternGraph partB) E) :
      Embedding B E.wholeMaskPartialDecode :=
    Embedding.ofWholeMaskPatternGraph B partB hTransB E
      hUnique hDomain f
  intro χ
  obtain ⟨βOld, hMono⟩ := hArrow (fun f => χ (decodeA f))
  let β : Embedding B E.wholeMaskPartialDecode := decodeB βOld
  refine ⟨β, ?_⟩
  intro α₁ α₂ hPart₁ hPart₂
  have hCompose (α : Embedding A B)
      (hPart : ∀ x : U, partB (α.toFun x) = partA x) :
      decodeA (βOld.comp
        (α.wholeMaskPatternGraph partA partB hPart)) =
        β.comp α := by
    apply Embedding.ext_toFun
    intro x
    rfl
  let a₁Old : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) :=
    α₁.wholeMaskPatternGraph partA partB hPart₁
  let a₂Old : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) :=
    α₂.wholeMaskPatternGraph partA partB hPart₂
  have hm := hMono a₁Old a₂Old
  change χ (decodeA (βOld.comp a₁Old)) =
    χ (decodeA (βOld.comp a₂Old)) at hm
  rw [hCompose α₁ hPart₁, hCompose α₂ hPart₂] at hm
  exact hm

/-- The verified final U-closed and protected B-copy coverage theorem
provides ALL uniqueness and domain hypotheses needed above. This
gives the final genuinely partial function arrow from a RELATIONAL
complete-mask arrow, without an intermediate functional tree. -/
theorem PartPreservingArrow.ofCoveredWholeMaskRelationalArrow
    (A : PartialSetStructure L U) [Finite U]
    (B : PartialSetStructure L V) [Finite V]
    (partA : U → P) (partB : V → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (C : RelStructure (L.wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (κ : Type*) (hArrow : StructuralRamsey.Arrow
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB)
      (wholeMaskTagReduct C) κ) :
    PartPreservingArrow A B
      (wholeMaskTagReduct C).wholeMaskPartialDecode
      partA partB κ := by
  apply PartPreservingArrow.ofWholeMaskRelationalArrow
    A B partA partB hTransA hTransB (wholeMaskTagReduct C)
    (fun F xs S T hS hT =>
      wholeMaskValue_unique_of_closed_coverage
        C Base basePart hClosed hPos hCover F xs S T hS hT)
    (fun F xs =>
      wholeMaskPartialDecode_defined_iff_OLD_domain_of_closed_coverage
        C Base basePart hClosed hPos hCover F xs)
    κ hArrow

/-- The second 2019 closed partite pass yields a Ramsey arrow
IN THE FULL-ROOT TAGGED LANGUAGE. Forgetting those extra tags,
then applying final B-copy normalization, gives the genuine
functional part-preserving arrow on the same final carrier.

No assumption that intermediate strict relational pictures decode
to functional B-trees appears in this theorem. -/
theorem PartPreservingArrow.ofCoveredWholeMaskTaggedArrow
    (A : PartialSetStructure L U) [Finite U]
    (B : PartialSetStructure L V) [Finite V]
    (partA : U → P) (partB : V → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (C : RelStructure (L.wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (κ : Type*) (hArrow : StructuralRamsey.Arrow
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph partA))
      (wholeMaskTagExpansion (B.wholeMaskPatternGraph partB))
      C κ) :
    PartPreservingArrow A B
      (wholeMaskTagReduct C).wholeMaskPartialDecode
      partA partB κ := by
  have hOldArrow : StructuralRamsey.Arrow
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB)
      (wholeMaskTagReduct C) κ :=
    wholeMaskTag_forget_arrow
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) C κ hArrow
  exact PartPreservingArrow.ofCoveredWholeMaskRelationalArrow
    A B partA partB hTransA hTransB
    C Base basePart hClosed hPos hCover κ hOldArrow

end StructuralRamsey.PartialSetStructure

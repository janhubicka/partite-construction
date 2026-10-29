import PartiteConstruction.Functional.WholeMaskExactWeakToUniqueDecodedTarget2019
import PartiteConstruction.Functional.WholeMaskCanonicalEmbeddingInverse2019

/-!
# A reusable exact hereditary complete-value coherence condition

The final 2019 exact weak local-map decoder (PR #526) requires the
target OLD complete-mask graph to have at most ONE entire output
vertex set over each primitive partial-function input.

Here that condition is given a named reusable predicate. It holds
for every canonical genuinely partial transversal source, and is
preserved by FULL OLD relational embeddings and hence by inducing on
an ARBITRARY exact weak subset. It also holds for the final U-closed
B-covered tagged 2019 Ramsey picture.

This proves that value coherence is a legitimate hereditary
semantic invariant to demand of completion targets, separate from
part labels, defined-empty domain completeness, tag normality
and actual K-class membership. It does NOT prove arbitrary
relational K-members satisfy this invariant, nor does it imply
full embeddings of arbitrary intrinsically irreducible weak tests.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w} {W : Type z}

/-- Every complete OLD graph witness for a fixed primitive function
and input tuple specifies the same ENTIRE set of output vertices;
no requirement on extra OLD active domain predicates is imposed. -/
def HasUniqueWholeMaskValues
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (U T : Set V),
    HasWholeMaskValue E F xs U →
    HasWholeMaskValue E F xs T → U = T

/-- A genuine partial Option(Set) source has coherent whole values,
including defined-empty and repeated argument tuples. -/
theorem PartialSetStructure.wholeMaskPatternGraph_hasUniqueValues
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P)
    (hTrans : PartialSetStructure.FibreTransversal A part) :
    HasUniqueWholeMaskValues (A.wholeMaskPatternGraph part) := by
  intro F xs U T hU hT
  have hOne : A.func F xs = some U :=
    (A.hasWholeMaskValue_iff_source_func_some
      part hTrans F xs U).mp hU
  have hTwo : A.func F xs = some T :=
    (A.hasWholeMaskValue_iff_source_func_some
      part hTrans F xs T).mp hT
  exact Option.some.inj (hOne.symm.trans hTwo)

namespace HasUniqueWholeMaskValues

/-- Full OLD induced embeddings pull back complete-value coherence.
In particular this does not require their images to be U-closed. -/
theorem ofEmbedding
    {E : RelStructure (L.wholeMaskPatternLanguage P) V}
    {D : RelStructure (L.wholeMaskPatternLanguage P) W}
    (hD : HasUniqueWholeMaskValues D)
    (e : Embedding E D) :
    HasUniqueWholeMaskValues E := by
  intro F xs U T hU hT
  have hBU : HasWholeMaskValue D F (e ∘ xs)
      (Structure.imageSet e U) :=
    e.map_hasWholeMaskValue F xs U hU
  have hBT : HasWholeMaskValue D F (e ∘ xs)
      (Structure.imageSet e T) :=
    e.map_hasWholeMaskValue F xs T hT
  have hImage : Structure.imageSet e U = Structure.imageSet e T :=
    hD F (e ∘ xs) (Structure.imageSet e U)
      (Structure.imageSet e T) hBU hBT
  ext x
  constructor
  · intro hx
    have hmem : e x ∈ Structure.imageSet e U := ⟨x, hx, rfl⟩
    rw [hImage] at hmem
    obtain ⟨y, hy, heq⟩ := hmem
    have hxy : y = x := e.injective heq
    simpa only [hxy] using hy
  · intro hx
    have hmem : e x ∈ Structure.imageSet e T := ⟨x, hx, rfl⟩
    rw [← hImage] at hmem
    obtain ⟨y, hy, heq⟩ := hmem
    have hxy : y = x := e.injective heq
    simpa only [hxy] using hy

/-- Uniqueness of COMPLETE value sets survives literal induced weak
restriction to ANY exact vertex subset, even when domain masks persist. -/
theorem induce
    {E : RelStructure (L.wholeMaskPatternLanguage P) V}
    (hE : HasUniqueWholeMaskValues E) (S : Set V) :
    HasUniqueWholeMaskValues (E.induce S) :=
  hE.ofEmbedding (inclusion E S)

end HasUniqueWholeMaskValues

/-- The ALREADY verified final B-covered 2019 target supplies this
same exact entire-value coherence, without source canonicality. -/
theorem wholeMask_hasUniqueValues_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part)))) :
    HasUniqueWholeMaskValues (wholeMaskTagReduct C) := by
  intro F xs U T hU hT
  exact wholeMaskValue_unique_of_closed_coverage
    C Base part hC hPos hCover F xs U T hU hT

end StructuralRamsey.RelStructure

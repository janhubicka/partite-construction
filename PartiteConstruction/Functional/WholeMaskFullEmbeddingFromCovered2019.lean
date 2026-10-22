import PartiteConstruction.Functional.WholeMaskOldEmbeddingTransport2019
import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019

/-!
# FULL old relational B-copies become genuine partial-function embeddings

The final U-closed 2019 picture is normalized only at the END, under
protected closed U-irreducible canonical B-copy coverage. Its old
complete-mask reduct decodes to genuine Option(Set)-valued functions
with unique whole values and exact domain activation.

If a finite genuine transversal partial-function source A embeds
FULLY into the OLD complete-mask reduct of such a target, the SAME
vertex map is a genuinely FULL partial-function embedding into
the decoded target. The key reflection is domain-sensitive: a
source-defined complete output tuple maps to the COMPLETE target
value; a source-undefined input cannot become defined because its
target OLD domain root would reflect into the canonical source OLD
domain, even if it uses a DIFFERENT surjective equality pattern.

This is the missing copywise full-embedding interpretation for
the final normalized target; it is NOT a claim that weak EHN
projections reflect absent domains, and it does not construct
strict functional B-tree target completions of mixed weak tests.
All original vertices and function outputs are used unchanged.
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- A FULL OLD relational embedding of the complete-mask graph of a
finite genuine transverse source into any OLD target with unique
complete values and exact OLD-domain decoding produces a FULL
genuinely partial Option(Set) function embedding on the SAME map.
Both undefined and defined-empty states are reflected faithfully. -/
noncomputable def ofWholeMaskPatternGraph
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (E : RelStructure (L.wholeMaskPatternLanguage P) W)
    (hUnique : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W) (U T : Set W),
      HasWholeMaskValue E F xs U →
      HasWholeMaskValue E F xs T → U = T)
    (hDomain : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W),
      E.wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain E F xs)
    (f : RelStructure.Embedding (A.wholeMaskPatternGraph part) E) :
    Embedding A E.wholeMaskPartialDecode where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R xs
    exact f.map_rel_iff (.inl R) xs
  map_func := by
    classical
    intro F xs
    cases hA : A.func F xs with
    | none =>
        have hNoSourceDomain :
            ¬ HasWholeMaskDomain (A.wholeMaskPatternGraph part) F xs := by
          intro hOld
          obtain ⟨U,hU⟩ :=
            (A.hasWholeMaskDomain_iff_sourceDefined
              part hTrans F xs).mp hOld
          rw [hA] at hU
          cases hU
        have hNoTargetDefined :
            ¬ E.wholeMaskPartialDecode.Defined F (f ∘ xs) := by
          intro hDef
          have hTargetDomain : HasWholeMaskDomain E F (f ∘ xs) :=
            (hDomain F (f ∘ xs)).mp hDef
          exact hNoSourceDomain
            ((f.hasWholeMaskDomain_map_iff F xs).mpr hTargetDomain)
        have hTargetNone :
            E.wholeMaskPartialDecode.func F (f ∘ xs) = none := by
          cases hVal : E.wholeMaskPartialDecode.func F (f ∘ xs) with
          | none => exact hVal
          | some U => exact (hNoTargetDefined ⟨U,hVal⟩).elim
        simpa only [hA, Option.map_none] using hTargetNone.symm
    | some U =>
        have hSource : HasWholeMaskValue
            (A.wholeMaskPatternGraph part) F xs U :=
          (A.hasWholeMaskValue_iff_source_func_some
            part hTrans F xs U).mpr hA
        have hValue : HasWholeMaskValue E F (f ∘ xs)
            (Structure.imageSet f U) :=
          f.map_hasWholeMaskValue F xs U hSource
        have hTargetSome :
            E.wholeMaskPartialDecode.func F (f ∘ xs) =
              some (Structure.imageSet f U) :=
          (E.wholeMaskPartialDecode_func_some_iff
            F (f ∘ xs) (hUnique F (f ∘ xs))
            (Structure.imageSet f U)).mpr hValue
        simpa only [hA, Option.map_some] using hTargetSome.symm

/-- In a FINAL U-closed canonical-B-covered positive-arity target,
no extra normality/domain-coherence premises are needed: the merged
covered-target decoding theorem supplies them. A FULL OLD embedding
of a genuine finite source is automatically an actual FULL partial
function embedding into the decoded final target. -/
noncomputable def ofCoveredWholeMaskPatternGraph
    {Q : Type w}
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (C : RelStructure (L.wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L Q) (partBase : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph partBase))))
    (f : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA) (wholeMaskTagReduct C)) :
    Embedding A (wholeMaskTagReduct C).wholeMaskPartialDecode :=
  ofWholeMaskPatternGraph A partA hTransA (wholeMaskTagReduct C)
    (fun F xs U T hU hT =>
      wholeMaskValue_unique_of_closed_coverage
        C Base partBase hC hPos hCover F xs U T hU hT)
    (fun F xs =>
      wholeMaskPartialDecode_defined_iff_OLD_domain_of_closed_coverage
        C Base partBase hC hPos hCover F xs)
    f

/-- A FULL embedded canonical tagged B-copy inside the final
B-covered U-closed target becomes a FULL genuine partial function
copy on EXACTLY its original vertices. No target fibre extension
is added, and the source's defined-empty applications remain
defined-empty. -/
noncomputable def ofCoveredWholeMaskTag
    {Q : Type w}
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (C : RelStructure (L.wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L Q) (partBase : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph partBase))))
    (f : RelStructure.Embedding
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph partA)) C) :
    Embedding A (wholeMaskTagReduct C).wholeMaskPartialDecode :=
  ofCoveredWholeMaskPatternGraph
    A partA hTransA C Base partBase hC hPos hCover
    f.wholeMaskTagReduct

end StructuralRamsey.PartialSetStructure.Embedding

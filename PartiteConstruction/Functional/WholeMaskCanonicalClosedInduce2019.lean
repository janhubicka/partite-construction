import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019
import PartiteConstruction.Structure.PartialSetFunctionsClosed
import PartiteConstruction.Functional.WholeMaskTagInduce2019

/-!
# Generated 2019 B-boundaries are actual canonical functional substructures

The verified two-pass 2019 proof uses a generated CLOSED boundary of
the reference Base as its target-side witness for compatible weak
root embeddings. Under the whole-mask presentation, a genuinely
partial-function closed boundary of the Base has exactly the same OLD
and fresh-tag relational interpretations as inducing the ambient
canonical Base graph on that same closed carrier.

The proof uses full part-preserving partial-function closed inclusion
and the verified full complete-mask graph embedding functor. Defined
empty values are preserved; no extra vertex is inserted. In particular
we never identify an UN-CLOSED weak restriction with its ambient old
domain records, because that assertion is generally false.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- For a genuinely partial function-CLOSED subset S, the canonical
OLD complete-mask relational representation of the ACTUAL full
functional substructure is literally the ambient OLD graph induced
on exactly S, including all active domain records and some-empty. -/
theorem wholeMaskPatternGraph_induceClosed_eq_induce
    (A : PartialSetStructure L V)
    (part : V → P) (S : Set V) (hS : A.IsClosed S) :
    (A.induceClosed S hS).wholeMaskPatternGraph
      (part ∘ Subtype.val) =
      (A.wholeMaskPatternGraph part).induce S := by
  let e : Embedding (A.induceClosed S hS) A :=
    A.closedInclusion S hS
  let eOld : RelStructure.Embedding
      ((A.induceClosed S hS).wholeMaskPatternGraph
        (part ∘ Subtype.val))
      (A.wholeMaskPatternGraph part) :=
    e.wholeMaskPatternGraph (part ∘ Subtype.val) part (fun _ => rfl)
  apply rel_injective
  funext R xs
  exact propext (eOld.map_rel_iff R xs).symm

/-- Fresh 2019 full-root tags also commute with this genuine CLOSED
functional restriction. This is the exact canonical boundary used
in the verified 2019 profile completion lemma, not an arbitrary
partial weak subset carrying fictitious domain bits. -/
theorem wholeMaskTagExpansion_induceClosed_eq_induce
    (A : PartialSetStructure L V)
    (part : V → P) (S : Set V) (hS : A.IsClosed S) :
    wholeMaskTagExpansion
      ((A.induceClosed S hS).wholeMaskPatternGraph
        (part ∘ Subtype.val)) =
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S := by
  calc
    wholeMaskTagExpansion
      ((A.induceClosed S hS).wholeMaskPatternGraph
        (part ∘ Subtype.val)) =
      wholeMaskTagExpansion ((A.wholeMaskPatternGraph part).induce S) := by
        rw [A.wholeMaskPatternGraph_induceClosed_eq_induce part S hS]
    _ = (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S :=
      wholeMaskTagExpansion_induce_eq (A.wholeMaskPatternGraph part) S

end StructuralRamsey.PartialSetStructure

import PartiteConstruction.Functional.NativeUClosedExactDictionary

/-!
# Full native embeddings transport ambient U-pattern data on exact weak sets

For a genuine FULL relation/set-valued-function embedding e:A↪B
and ANY exact weak vertex set S⊆B, the induced AMBIENT
canonical tagged U-pattern structures on e⁻¹[S] and S
are connected by a FULL relational embedding on the
literal vertex map e.

This retains original relations, actual ambient domain-root
relations, output graph tuples, and every fresh FULL
positive input-pattern U-closure tag. Unlike recomputing
domain relations from native weakly induced function fibres,
the induced AMBIENT tagged model remembers every active
root even when its output lies outside the tested vertex set.

No closure hull, singleton-valuedness, function arity
restriction, projection-domain reflection, or artificial
target completion is required. The map is a literal
restriction of the already verified full tagged embedding
(e.patternGraph).patternTag.

This is the exact map-level counterpart of the checked
2019 U-substructure/weak-test induction and is intended
for the FULL copied maps of native Hales–Jewett attachments.
It does NOT apply to a merely EHN original-partial map
with extra target-defined source-undefined function inputs.
-/

namespace StructuralRamsey.Structure.Embedding

open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {V W : Type v}
variable {A : Structure L V} {B : Structure L W}

/-- A FULL native functional embedding restricts to a FULL
embedding of the AMBIENT tagged 2019 closure-pattern
relational records on exact weak vertex preimages.

All old domain bits, every function output graph incidence,
and fresh complete-root closure tags are reflected. The
source carrier is exactly e⁻¹[S]; no generated closure is
adjoined even when this subset is not function-closed. -/
noncomputable def taggedPatternWeakPreimage
    (e : Embedding A B) (S : Set W) :
    RelStructure.Embedding
      ((patternTagExpansion A.patternGraph).induce (e.toFun ⁻¹' S))
      ((patternTagExpansion B.patternGraph).induce S) where
  toFun := fun x => ⟨e x.1, x.2⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro R xs
    change (patternTagExpansion B.patternGraph).rel R
        (e.toFun ∘ (Subtype.val ∘ xs)) ↔
      (patternTagExpansion A.patternGraph).rel R
        (Subtype.val ∘ xs)
    exact ((e.patternGraph).patternTag).map_rel_iff R
      (Subtype.val ∘ xs)

end StructuralRamsey.Structure.Embedding

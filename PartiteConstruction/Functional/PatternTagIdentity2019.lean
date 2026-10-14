import PartiteConstruction.Functional.PatternDomainCoherence2019

/-!
# Exact identity between normal tagged structures and canonical expansions

Normality of a fresh 2019 function-root tag does not merely imply
a one-sided homomorphism: the tagged structure is FULLY and
IDENTICALLY isomorphic to the canonical tag expansion of its OLD
reduct.

These full embeddings reuse the SAME vertex map in both directions.
They make the OLD induced-root embeddings supplied by actual domains
available as full embeddings into a final (possibly noncanonical)
tagged Picture once its local laws have been verified.

No closure hull or extra vertex is introduced.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A normal tagged structure is an induced/full image of the canonical
tag expansion of its own old-domain/output reduct, on identity vertices. -/
def PatternTagNormal.canonicalEmbedding
    {E : RelStructure (L.patternTag) V}
    (h : PatternTagNormal E) :
    Embedding (patternTagExpansion (patternTagReduct E)) E where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    rcases R with R | p
    · exact Iff.rfl
    · simpa only [Function.id_comp] using h p xs

/-- Conversely, a normal tagged structure embeds fully back into its
canonical expansion with the identical vertex map. -/
def PatternTagNormal.toCanonicalEmbedding
    {E : RelStructure (L.patternTag) V}
    (h : PatternTagNormal E) :
    Embedding E (patternTagExpansion (patternTagReduct E)) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    rcases R with R | p
    · exact Iff.rfl
    · simpa only [Function.id_comp] using (h p xs).symm

end StructuralRamsey.RelStructure

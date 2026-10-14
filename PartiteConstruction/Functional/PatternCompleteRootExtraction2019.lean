import PartiteConstruction.Functional.PatternClosureCanonical2019

/-!
# Extract the exact FULL induced old root pattern of an active domain

Every valid (nonempty, injectively enumerated) OLD function-domain
tuple determines a canonical COMPLETE root pattern: pull back every
old relation along its exact distinct-input enumeration.

This constructs the missing full root for arbitrary OLD relational
structures, not only canonical graphs of genuine functions. The
root embeds fully into the original OLD structure, and its canonical
tagged expansion embeds fully into the canonical tagged structure.

A valid OLD output tuple over this domain consequently receives its
corresponding fresh tag, provided it has a true domain relation.
No closure vertices or additional test vertices are introduced.
-/

namespace StructuralRamsey

open StructuralRamsey.RelStructure

universe u v

namespace Language.FunctionRootPattern

variable {L : Language.{u}} {V : Type v}

/-- The complete induced OLD root pattern of a specified active
function-domain tuple, on its actual distinct root vertices. -/
def ofActiveDomain
    (E : RelStructure (L.patternGraph) V)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hDomain : E.rel (.inr (.inl p)) root) :
    Language.FunctionRootPattern L where
  input := p
  positive := hpos
  root := {
    rel R xs := E.rel R (root ∘ xs)
  }
  hasDomain := hDomain

/-- The full OLD root embeds back on EXACTLY the original vertices,
provided the displayed root tuple lists distinct vertices. -/
def ofActiveDomain_embedding
    (E : RelStructure (L.patternGraph) V)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (hDomain : E.rel (.inr (.inl p)) root) :
    Embedding (ofActiveDomain E p hpos root hDomain).root E where
  toFun := root
  injective := hinj
  map_rel_iff := by
    intro R xs
    rfl

/-- After canonical tagging, the full OLD root still embeds, and its
image is exactly the original root tuple, not a generated hull. -/
noncomputable def ofActiveDomain_tagEmbedding
    (E : RelStructure (L.patternGraph) V)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (hDomain : E.rel (.inr (.inl p)) root) :
    Embedding
      (RelStructure.patternTagExpansion
        (ofActiveDomain E p hpos root hDomain).root)
      (RelStructure.patternTagExpansion E) :=
  (ofActiveDomain_embedding E p hpos root hinj hDomain).patternTag

end Language.FunctionRootPattern

namespace RelStructure

variable {L : Language.{u}} {V : Type v}

/-- Any valid OLD output graph tuple over an active positive root
has its canonical fresh complete-root tag. The OLD domain and the
actual input-prefix injection are hypotheses, not invented from
an inconsistent graph tuple. -/
theorem patternTagExpansion_tag_of_valid_old_output
    (E : RelStructure (L.patternGraph) V)
    (p : Language.FunctionInputPattern L)
    (hpos : 0 < p.rootSize)
    (t : Fin (p.rootSize + 1) → V)
    (hOld : E.rel (.inr (.inr p)) t)
    (hinj : Function.Injective
      (fun i : Fin p.rootSize => t i.castSucc))
    (hDom : E.rel (.inr (.inl p))
      (fun i : Fin p.rootSize => t i.castSucc)) :
    (patternTagExpansion E).rel
      (.inr (Language.FunctionRootPattern.ofActiveDomain
        E p hpos (fun i : Fin p.rootSize => t i.castSucc) hDom)) t := by
  constructor
  · exact hOld
  · refine ⟨Language.FunctionRootPattern.ofActiveDomain_embedding
      E p hpos (fun i : Fin p.rootSize => t i.castSucc) hinj hDom,
      ?_⟩
    intro i
    rfl

end RelStructure
end StructuralRamsey

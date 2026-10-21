import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns
import PartiteConstruction.Ramsey.ClosureDescription2019
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Fresh 2019 closure symbols for complete whole-value root patterns

For each active (function input equality pattern, full output-part mask)
record the FULL induced old relational structure on the DISTINCT input
vertices. This includes the appropriate mask-domain predicate and any
old relation/graph tuples internal to that root. Each such full root
pattern has its own fresh positive-output closure relation.

A mask of length zero is a defined-empty DOMAIN relation, not a closure
rule (the 2019 rule requires root size < total tuple arity).
Nullary inputs likewise require the separate nullary-root reduction.
No arbitrary relational target is decoded in this syntax module.
-/

namespace StructuralRamsey

universe u v

namespace Language

/-- A whole-value active input root with its full OLD induced relational
pattern; neither the primitive argument tuple nor its output set is
required to be disjoint. -/
structure WholeMaskRootPattern (L : Language.{u}) (P : Type v)
    [Fintype P] where
  input : FunctionInputPattern L
  mask : CompleteOutputParts P
  rootPositive : 0 < input.rootSize
  outputPositive : 0 < mask.size
  root : RelStructure (L.wholeMaskPatternLanguage P)
    (Fin input.rootSize)
  hasDomain : root.rel (.inr (.inl (input, mask))) id

/-- Keep every old relation unchanged and add one closure relation for
each FULL active old root pattern with a nonempty complete value. -/
def wholeMaskTagLanguage (L : Language.{u}) (P : Type v)
    [Fintype P] : RelLanguage.{max u v} where
  Symbol := (L.wholeMaskPatternLanguage P).Symbol ⊕
    WholeMaskRootPattern L P
  arity
    | .inl R => (L.wholeMaskPatternLanguage P).arity R
    | .inr p => p.input.rootSize + p.mask.size

end Language

namespace RelStructure

variable {L : Language.{u}} {P : Type v} {V : Type*}
variable [Fintype P]

/-- Canonical tag of a complete output tuple whose distinct input prefix
fully realizes the stored OLD root structure, including mask activation. -/
def wholeMaskTagExpansion
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) :
    RelStructure (L.wholeMaskTagLanguage P) V where
  rel
    | .inl R, xs => E.rel R xs
    | .inr p, xs =>
        E.rel (.inr (.inr (p.input, p.mask))) xs ∧
          ∃ e : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs (Fin.castAdd p.mask.size i) = e i

/-- The old complete-mask/domain interpretation can always be recovered
by forgetting ONLY the fresh closure-relation symbols. -/
def wholeMaskTagReduct
    (E : RelStructure (L.wholeMaskTagLanguage P) V) :
    RelStructure (L.wholeMaskPatternLanguage P) V where
  rel R xs := E.rel (.inl R) xs

end RelStructure

namespace Language.WholeMaskRootPattern

variable {L : Language.{u}} {P : Type v} [Fintype P]

/-- The 2019 closure rule attached to one complete-value mask with a
full induced old input-root pattern. Its root irreducibility is witnessed
by the active domain-mask relation spanning all distinct input vertices. -/
def closureRule (p : WholeMaskRootPattern L P) :
    RelStructure.ClosureRule (L.wholeMaskTagLanguage P) where
  symbol := .inr p
  rootSize := p.input.rootSize
  rootPositive := p.rootPositive
  rootStrict := by
    change p.input.rootSize < p.input.rootSize + p.mask.size
    have hPositive : 0 < p.mask.size := p.outputPositive
    omega
  root := RelStructure.wholeMaskTagExpansion p.root
  rootIrreducible := by
    intro x y hxy
    refine ⟨.inl (.inr (.inl (p.input, p.mask))),
      (fun i : Fin p.input.rootSize => i), x, y, ?_, rfl, rfl⟩
    exact p.hasDomain

end Language.WholeMaskRootPattern

namespace Language

/-- Fresh 2019 closure description for every full active old input root
with a POSITIVE output mask. Empty-valued domains are retained as old
relations but impose no output-vertex closure rule. -/
def wholeMaskClosureRules (L : Language.{u}) (P : Type v)
    [Fintype P] :
    RelStructure.ClosureDescription (L.wholeMaskTagLanguage P) :=
  Set.range WholeMaskRootPattern.closureRule

end Language

end StructuralRamsey

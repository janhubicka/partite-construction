import PartiteConstruction.Functional.PartialFunctionPatternDecode2019
import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# Fresh closure symbols for FULL partial-function root patterns

For the 2019 closure-description representation, one cannot assign
different induced root patterns to the SAME old function-graph symbol.
Instead use one FRESH closure relation for every:

* function input equality pattern p, including repeated arguments;
* full induced OLD relational structure on its distinct positive root;
* distinguished true domain relation for p.

The new closure root is the CANONICAL tagged expansion of that full
old root pattern. Thus it faithfully reflects every old and tagged
relation on the root and witnesses irreducibility through the domain
tuple. This is the syntax and the irreducible-root constructor.

A separate local normality/validity theorem is required to establish
that arbitrary final U-closed tagged Pictures decode to coherent
singleton-valued primitive functions. No such assertion is assumed
here.
-/

namespace StructuralRamsey

open StructuralRamsey.RelStructure

universe u v

namespace Language

/-- Exact OLD input-root pattern carrying a nonempty function domain.
The carrier Fin(rootSize) indexes distinct vertices, not input
positions (repetitions are stored by input.argMap).
Positive size is required by the 2019 closure-description interface. -/
structure FunctionRootPattern (L : Language.{u}) where
  input : FunctionInputPattern L
  positive : 0 < input.rootSize
  root : RelStructure (L.patternGraph) (Fin input.rootSize)
  hasDomain : root.rel (.inr (.inl input)) id

/-- Every complete OLD function-input root pattern has its own FRESH
closure symbol, rather than sharing one unchanged output-graph
relation among incompatible induced root patterns. -/
def patternTag (L : Language.{u}) : RelLanguage.{u} where
  Symbol := (L.patternGraph).Symbol ⊕ FunctionRootPattern L
  arity
    | .inl R => (L.patternGraph).arity R
    | .inr p => p.input.rootSize + 1

end Language

namespace RelStructure

variable {L : Language.{u}} {V : Type v}

/-- Canonical tagging, computed strictly from the underlying OLD
input-pattern graph. A new tag holds when the old output tuple is
present and its distinct root prefix FULLY realizes the prescribed
old induced root structure. -/
def patternTagExpansion
    (E : RelStructure (L.patternGraph) V) :
    RelStructure (L.patternTag) V where
  rel
    | .inl R, xs => E.rel R xs
    | .inr p, xs =>
        E.rel (.inr (.inr p.input)) xs ∧
          ∃ e : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs i.castSucc = e i

/-- Forget all fresh closure tags; retain the original relation,
domain and output-graph symbols. -/
def patternTagReduct
    (E : RelStructure (L.patternTag) V) :
    RelStructure (L.patternGraph) V where
  rel R xs := E.rel (.inl R)

end RelStructure

namespace Language.FunctionRootPattern

variable {L : Language.{u}}

/-- The 2019 closure rule assigned to one FULL OLD input pattern.
Its root is the CANONICALLY TAGGED version of the original root,
with a complete domain incidence witnessing ordinary irreducibility. -/
def closureRule (p : FunctionRootPattern L) :
    ClosureRule (L.patternTag) where
  symbol := .inr p
  rootSize := p.input.rootSize
  rootPositive := p.positive
  rootStrict := Nat.lt_succ_self _
  root := RelStructure.patternTagExpansion p.root
  rootIrreducible := by
    intro x y hxy
    refine ⟨.inl (.inr (.inl p.input)),
      (fun i : Fin p.input.rootSize => i), x, y, ?_, rfl, rfl⟩
    exact p.hasDomain

end Language.FunctionRootPattern

namespace Language

/-- Full closure description: precisely the fresh tagged rules of
the distinct positive input-root patterns. -/
def patternClosureRules (L : Language.{u}) :
    ClosureDescription (L.patternTag) :=
  Set.range Language.FunctionRootPattern.closureRule

end Language

end StructuralRamsey

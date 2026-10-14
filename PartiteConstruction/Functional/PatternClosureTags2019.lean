import PartiteConstruction.Functional.PartialFunctionPatternDecode2019
import PartiteConstruction.Ramsey.ClosureDescription2019
import PartiteConstruction.Iterated.LocalTreeLike

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

universe u v w

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
  rel R xs := E.rel (.inl R) xs

end RelStructure

namespace RelStructure.Embedding

variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {E : RelStructure (L.patternGraph) V}
variable {F : RelStructure (L.patternGraph) W}

/-- Canonical full pattern-root tags preserve and REFLECT full
embeddings of the old relational structures. Reflection works
because every root vertex of a tag is one of the displayed prefix
vertices, hence already lies in the embedded source image. -/
noncomputable def patternTag (f : Embedding E F) :
    Embedding (RelStructure.patternTagExpansion E)
      (RelStructure.patternTagExpansion F) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | p
    · exact f.map_rel_iff R xs
    · change
        (F.rel (.inr (.inr p.input)) (f ∘ xs) ∧
          ∃ g : Embedding p.root F,
            ∀ i : Fin p.input.rootSize,
              (f ∘ xs) i.castSucc = g i) ↔
        (E.rel (.inr (.inr p.input)) xs ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs i.castSucc = g i)
      constructor
      · rintro ⟨hOldF, gF, hPrefixF⟩
        have hOldE : E.rel (.inr (.inr p.input)) xs :=
          (f.map_rel_iff (.inr (.inr p.input)) xs).mp hOldF
        let q : Fin p.input.rootSize → V :=
          fun i => xs i.castSucc
        let gE : Embedding p.root E := {
          toFun := q
          injective := by
            intro i j hij
            apply gF.injective
            calc
              gF i = f (q i) := (hPrefixF i).symm
              _ = f (q j) := congrArg f hij
              _ = gF j := hPrefixF j
          map_rel_iff := by
            intro S ys
            have hEq : f ∘ (q ∘ ys) = gF ∘ ys := by
              funext i
              exact hPrefixF (ys i)
            calc
              E.rel S (q ∘ ys) ↔ F.rel S (f ∘ (q ∘ ys)) :=
                (f.map_rel_iff S (q ∘ ys)).symm
              _ ↔ F.rel S (gF ∘ ys) := by rw [hEq]
              _ ↔ p.root.rel S ys := gF.map_rel_iff S ys
        }
        exact ⟨hOldE, gE, fun _ => rfl⟩
      · rintro ⟨hOldE, gE, hPrefixE⟩
        have hOldF : F.rel (.inr (.inr p.input)) (f ∘ xs) :=
          (f.map_rel_iff (.inr (.inr p.input)) xs).mpr hOldE
        refine ⟨hOldF, f.comp gE, ?_⟩
        intro i
        exact congrArg f (hPrefixE i)

/-- Forget the fresh closure tags from a full embedding, retaining
all the old domain and output graph relations. -/
def patternTagReduct
    {A : RelStructure (L.patternTag) V}
    {B : RelStructure (L.patternTag) W}
    (f : Embedding A B) :
    Embedding (RelStructure.patternTagReduct A)
      (RelStructure.patternTagReduct B) where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R xs => f.map_rel_iff (.inl R) xs

end RelStructure.Embedding

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

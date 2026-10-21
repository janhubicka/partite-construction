import PartiteConstruction.Functional.PatternLanguageFinite
import PartiteConstruction.Structure.PartialSetFunctionsWholePartGraph

/-!
# Complete-output masks with full function-input equality patterns

The old relational language for a genuinely partial set-valued function
records separate domain-mask and COMPLETE output-tuple symbols for each
surjective equality pattern of the input and each injective list of output
parts. Every original relation is retained. A complete output tuple
implies the matching domain-mask tuple.

The old domain-mask relation deliberately survives induction to a weak
test even when its complete function value leaves the test. Recomputing
the mask domain from the weak restriction is in general WRONG. Only
complete output tuple relations commute with whole-fibre weak restriction.

The finiteness assertion requires both a finite original signature and a
finite part set. Fresh 2019 closure tags with irreducible full old roots
will be constructed separately; this file makes no U-closedness claim.
-/

namespace StructuralRamsey

universe u v w

namespace Language

/-- A function input equality pattern and a complete output-part tuple.
The output-part list has no repeated labels and length at most |P|. -/
abbrev WholeMaskPattern (L : Language.{u}) (P : Type v) [Fintype P] :=
  FunctionInputPattern L × CompleteOutputParts P

/-- Relational syntax: original relations, complete-mask domains on
distinct input vertices, and complete-mask output relations. -/
def wholeMaskPatternLanguage (L : Language.{u}) (P : Type v)
    [Fintype P] : RelLanguage.{max u v} where
  Symbol := L.RelSymbol ⊕
    ((WholeMaskPattern L P) ⊕ (WholeMaskPattern L P))
  arity
    | .inl R => L.relArity R
    | .inr (.inl (p, _)) => p.rootSize
    | .inr (.inr (p, q)) => p.rootSize + q.size

/-- Finite primitive symbols and finite parts give a finite
complete-mask equality-pattern signature. -/
instance wholeMaskPatternLanguage_finite
    (L : Language.{u}) (P : Type v)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (wholeMaskPatternLanguage L P).Symbol := by
  change Finite
    (L.RelSymbol ⊕
      ((WholeMaskPattern L P) ⊕ (WholeMaskPattern L P)))
  infer_instance

end Language

namespace PartialSetStructure

variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- The full old source data. The domain relation remembers the
exact output mask at each DISTINCT input root, including repeated
primitive function arguments through p.argMap. The graph relation
records every output vertex AT ONCE, not individual incidences. -/
def wholeMaskPatternGraph
    (A : PartialSetStructure L V) (part : V → P) :
    RelStructure (L.wholeMaskPatternLanguage P) V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr (.inl (p, q)), root =>
        Function.Injective root ∧
          ∃ U : Set V,
            A.func p.symbol (root ∘ p.argMap) = some U ∧
              part '' U = Set.range q.label
    | .inr (.inr (p, q)), xs =>
        Function.Injective
          (fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∧
        A.func p.symbol
          ((fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∘
            p.argMap) =
          some (Set.range (fun j : Fin q.size =>
            xs (Fin.natAdd p.rootSize j))) ∧
        ∀ j : Fin q.size,
          part (xs (Fin.natAdd p.rootSize j)) = q.label j

/-- Every complete output tuple has the corresponding active domain
mask on its exact distinct input root, including the empty mask. -/
theorem wholeMaskPatternGraph_output_has_domain
    (A : PartialSetStructure L V) (part : V → P)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (xs : Fin (p.rootSize + q.size) → V)
    (h : (A.wholeMaskPatternGraph part).rel (.inr (.inr (p, q))) xs) :
    (A.wholeMaskPatternGraph part).rel
      (.inr (.inl (p, q)))
      (fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) := by
  change
    Function.Injective (fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∧
    A.func p.symbol
      ((fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          xs (Fin.natAdd p.rootSize j))) ∧
    (∀ j : Fin q.size,
      part (xs (Fin.natAdd p.rootSize j)) = q.label j) at h
  change
    Function.Injective (fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∧
      ∃ U : Set V,
        A.func p.symbol
          ((fun i : Fin p.rootSize => xs (Fin.castAdd q.size i)) ∘
            p.argMap) = some U ∧
        part '' U = Set.range q.label
  refine ⟨h.1, ⟨Set.range (fun j : Fin q.size =>
    xs (Fin.natAdd p.rootSize j)), h.2.1, ?_⟩⟩
  ext a
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (h.2.2 j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨xs (Fin.natAdd p.rootSize j), ⟨j, rfl⟩, h.2.2 j⟩

/-- Only the complete-output tuple fragment commutes with WHOLE-fibre
deletion on an exact vertex set. Active domain masks must instead be
induced from the original ambient structure, NOT recomputed. -/
theorem wholeWeakInduce_wholeMaskPatternGraph_output_iff
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (xs : Fin (p.rootSize + q.size) → S) :
    ((wholeWeakInduce A S).wholeMaskPatternGraph
       (part ∘ Subtype.val)).rel (.inr (.inr (p, q))) xs ↔
      ((A.wholeMaskPatternGraph part).induce S).rel
        (.inr (.inr (p, q))) xs := by
  have hInj :
      Function.Injective (fun i : Fin p.rootSize =>
        xs (Fin.castAdd q.size i)) ↔
      Function.Injective (fun i : Fin p.rootSize =>
        (xs (Fin.castAdd q.size i)).1) := by
    constructor
    · intro h i j hij
      apply h
      exact Subtype.ext hij
    · intro h i j hij
      apply h
      exact congrArg Subtype.val hij
  change
    (Function.Injective (fun i : Fin p.rootSize =>
        xs (Fin.castAdd q.size i)) ∧
      wholeWeakValue S
        (A.func p.symbol ((fun i : Fin p.rootSize =>
          (xs (Fin.castAdd q.size i)).1) ∘ p.argMap)) =
        some (Set.range (fun j : Fin q.size =>
          xs (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin q.size,
        part (xs (Fin.natAdd p.rootSize j)).1 = q.label j)) ↔
    (Function.Injective (fun i : Fin p.rootSize =>
        (xs (Fin.castAdd q.size i)).1) ∧
      A.func p.symbol ((fun i : Fin p.rootSize =>
          (xs (Fin.castAdd q.size i)).1) ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          (xs (Fin.natAdd p.rootSize j)).1)) ∧
      (∀ j : Fin q.size,
        part (xs (Fin.natAdd p.rootSize j)).1 = q.label j))
  exact and_congr hInj
    (and_congr
      (wholeWeakValue_eq_some_range_iff S
        (A.func p.symbol ((fun i : Fin p.rootSize =>
          (xs (Fin.castAdd q.size i)).1) ∘ p.argMap))
        (fun j : Fin q.size => xs (Fin.natAdd p.rootSize j)))
      Iff.rfl)

end PartialSetStructure
end StructuralRamsey

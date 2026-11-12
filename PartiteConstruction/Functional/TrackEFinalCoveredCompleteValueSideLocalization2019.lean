import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Structure.PartialSetFunctions

/-!
# Track E: a decoded complete function incidence cannot cross an OLD free cover

In the ACTUAL final protected U-closed B-covered tagged 2019 source C,
every defined whole decoded function value has a genuine OLD complete
output relation tuple: its displayed input root contains every distinct
primitive input, and its output tuple enumerates the ENTIRE value set.
This statement is guaranteed by verified complete-value coherence;
C need not equal the canonical tag of the decoded source.

If all actual tagged relation tuples localize to one of two vertex
sets S/T, then each decoded positive functional incidence (the whole
primitive argument tuple plus any output vertex) is supported in ONE
of the two sides. No closure-hull substitution, no graph-clique
shortcut, no new native tree, and no global HE upgrade.

This is the missing *function-incidence localization* step toward
using native full irreducibility to rule out a nontrivial U-free cover
of an exact final tagged native irreducible test.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Any actual complete decoded function value in the final B-covered
tagged C has its primitive input coordinates and EACH output vertex
on one common side of an arbitrary side-localized tagged relation
cover. The sides themselves need not be function-closed for this step.
Entire fibres (including defined-empty) and repeated arguments are
kept exactly; the conclusion is vacuous for empty output values. -/
theorem wholeMaskCovered_decodedFunctionIncident_side
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S T : Set V)
    (hLoc : ∀ (R : (L.wholeMaskTagLanguage P).Symbol)
        (tuple : Fin ((L.wholeMaskTagLanguage P).arity R) → V),
      C.rel R tuple →
        (∀ k, tuple k ∈ S) ∨ (∀ k, tuple k ∈ T))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (U : Set V)
    (hValue :
      (wholeMaskTagReduct C).wholeMaskPartialDecode.func F xs = some U)
    (y : V) (hy : y ∈ U) :
    ((∀ i, xs i ∈ S) ∧ y ∈ S) ∨
      ((∀ i, xs i ∈ T) ∧ y ∈ T) := by
  classical
  let E : RelStructure (L.wholeMaskPatternLanguage P) V :=
    wholeMaskTagReduct C
  have hUnique (U' U'' : Set V)
      (hU' : HasWholeMaskValue E F xs U')
      (hU'' : HasWholeMaskValue E F xs U'') : U' = U'' :=
    wholeMaskValue_unique_of_closed_coverage
      C Base part hC hPos hCover F xs U' U'' hU' hU''
  obtain ⟨m, r, hr, q, t, hGraph, hArgs, hOutput⟩ :=
    (E.wholeMaskPartialDecode_func_some_iff
      F xs hUnique U).mp hValue
  let p : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  have hTagRel : C.rel (.inl (.inr (.inr (p,q)))) t := hGraph
  have hOneSide (Z : Set V)
      (hAll : ∀ k : Fin (m + q.size), t k ∈ Z) :
      (∀ i, xs i ∈ Z) ∧ y ∈ Z := by
    constructor
    · intro i
      rw [hArgs i]
      exact hAll (Fin.castAdd q.size (r i))
    · have hyValue : y ∈ Set.range
          (fun j : Fin q.size => t (Fin.natAdd m j)) := by
        rw [← hOutput]
        exact hy
      obtain ⟨j, hj⟩ := hyValue
      rw [← hj]
      exact hAll (Fin.natAdd m j)
  rcases hLoc (.inl (.inr (.inr (p,q)))) t hTagRel with hS | hT
  · exact Or.inl (hOneSide S hS)
  · exact Or.inr (hOneSide T hT)

/-- The same side-localization law, expressed for the genuine native
collapse of the Option(Set) decoder. Undefined inputs have no
incidences and defined-empty values contribute no output incidence.
No domain reflection or canonicality assumption is needed. -/
theorem wholeMaskCovered_nativeFunctionIncident_side
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S T : Set V)
    (hLoc : ∀ (R : (L.wholeMaskTagLanguage P).Symbol)
        (tuple : Fin ((L.wholeMaskTagLanguage P).arity R) → V),
      C.rel R tuple →
        (∀ k, tuple k ∈ S) ∨ (∀ k, tuple k ∈ T))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (y : V)
    (hy : y ∈ ((wholeMaskTagReduct C).wholeMaskPartialDecode.collapseDomain).func F xs) :
    ((∀ i, xs i ∈ S) ∧ y ∈ S) ∨
      ((∀ i, xs i ∈ T) ∧ y ∈ T) := by
  let A : PartialSetStructure L V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  cases hValue : A.func F xs with
  | none =>
      have hFalse : False := by
        change y ∈ (A.func F xs).getD ∅ at hy
        simp [hValue] at hy
      exact hFalse.elim
  | some U =>
      have hIn : y ∈ U := by
        change y ∈ (A.func F xs).getD ∅ at hy
        simpa [hValue] using hy
      exact wholeMaskCovered_decodedFunctionIncident_side
        C Base part hC hPos hCover S T hLoc F xs U hValue y hIn

end StructuralRamsey.RelStructure

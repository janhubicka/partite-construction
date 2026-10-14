import PartiteConstruction.Functional.TupleEqualityPattern2019

/-!
# Old relational language for partial functions with repeated arguments

The 2019 closure description needs one graph/domain relation for EACH
equality pattern of an input tuple. The coordinates of its closure
root are distinct even when the original function arguments repeat.

An input pattern consists of a function symbol F, a finite root Fin m
and a surjective repeat map Fin(arity F) -> Fin m. The old relational
language has separate domain and graph symbols for each pattern.

The canonical interpretation only accepts injective root enumerations.
Every finite nonempty function input has such an exact representation,
using the verified equality-pattern factorization lemma. The
root-size-0 case is recorded, but it must subsequently be handled
by a distinct nullary-root reduction because the literal 2019
closure-description rules require positive root size.

The fresh FULL ROOT PATTERN closure tags and the reverse decoding from
arbitrary final structures remain separate. Do not confuse this old
relational encoding with the final U-closed tagged language.
-/

namespace StructuralRamsey

universe u v

namespace Language

/-- The input equality pattern and the distinct vertices that form the
root of a partially defined function. -/
structure FunctionInputPattern (L : Language.{u}) where
  symbol : L.FuncSymbol
  rootSize : ℕ
  repeat : Fin (L.funcArity symbol) → Fin rootSize
  onto : Function.Surjective repeat

/-- Original relations, one domain relation and one graph relation
for each function symbol and each possible input equality pattern. -/
def patternGraph (L : Language.{u}) : RelLanguage.{u} where
  Symbol := L.RelSymbol ⊕ (FunctionInputPattern L ⊕ FunctionInputPattern L)
  arity
    | .inl R => L.relArity R
    | .inr (.inl p) => p.rootSize
    | .inr (.inr p) => p.rootSize + 1

end Language

namespace Structure

variable {L : Language.{u}} {V : Type v}

/-- Canonical pattern-indexed relational representation of an actual
partially defined (possibly set-valued) structure. Output incidence
is recorded on distinct roots with the original repeated inputs
reconstructed from the pattern map. -/
def patternGraph (A : Structure L V) :
    RelStructure (L.patternGraph) V where
  rel
    | .inl R, x => A.rel R x
    | .inr (.inl p), x =>
        Function.Injective x ∧ (A.func p.symbol (x ∘ p.repeat)).Nonempty
    | .inr (.inr p), x =>
        Function.Injective
          (fun i : Fin p.rootSize => x (Fin.castSucc i)) ∧
        x (Fin.last p.rootSize) ∈
          A.func p.symbol
            ((fun i : Fin p.rootSize => x (Fin.castSucc i)) ∘ p.repeat)

/-- Every nonempty source fibre has a domain witness on the EXACT
distinct-input root. The repeat map preserves all repeated
argument positions. No function-generated closure hull is added. -/
theorem patternGraph_domain_of_nonempty
    (A : Structure L V) [Finite V]
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V)
    (hx : (A.func F x).Nonempty) :
    ∃ (p : Language.FunctionInputPattern L)
      (e : Fin p.rootSize → V),
      Function.Injective e ∧
      (∀ i, x i = e (p.repeat i)) ∧
      (A.patternGraph).rel (.inr (.inl p)) e := by
  classical
  obtain ⟨m, r, e, hSurj, hInj, hFact, _hExact⟩ :=
    exists_tuple_equality_pattern_exact x
  let p : Language.FunctionInputPattern L := {
    symbol := F
    rootSize := m
    repeat := r
    onto := hSurj
  }
  refine ⟨p, e, hInj, hFact, ?_⟩
  change Function.Injective e ∧
    (A.func F (e ∘ r)).Nonempty
  refine ⟨hInj, ?_⟩
  have heq : e ∘ r = x := by
    funext i
    exact (hFact i).symm
  rw [heq]
  exact hx

end Structure
end StructuralRamsey

import PartiteConstruction.Functional.TupleEqualityPattern2019

/-!
# Old relational language for partial functions with repeated arguments

The 2019 closure description needs one graph/domain relation for EACH
equality pattern of an input tuple. The coordinates of its closure
root are distinct even when the original function arguments argMap.

An input pattern consists of a function symbol F, a finite root Fin m
and a surjective argMap map Fin(arity F) -> Fin m. The old relational
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
  argMap : Fin (L.funcArity symbol) → Fin rootSize
  onto : Function.Surjective argMap

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
        Function.Injective x ∧ (A.func p.symbol (x ∘ p.argMap)).Nonempty
    | .inr (.inr p), x =>
        Function.Injective
          (fun i : Fin p.rootSize => x (Fin.castSucc i)) ∧
        x (Fin.last p.rootSize) ∈
          A.func p.symbol
            ((fun i : Fin p.rootSize => x (Fin.castSucc i)) ∘ p.argMap)

/-- Every nonempty source fibre has a domain witness on the EXACT
distinct-input root. The argMap map preserves all repeated
argument positions. No function-generated closure hull is added. -/
theorem patternGraph_domain_of_nonempty
    (A : Structure L V) [Finite V]
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V)
    (hx : (A.func F x).Nonempty) :
    ∃ (m : ℕ) (r : Fin (L.funcArity F) → Fin m)
      (hSurj : Function.Surjective r) (e : Fin m → V),
      Function.Injective e ∧
      (∀ i, x i = e (r i)) ∧
      (A.patternGraph).rel (.inr (.inl
        ({ symbol := F, rootSize := m, argMap := r, onto := hSurj } :
          Language.FunctionInputPattern L))) e := by
  classical
  obtain ⟨m, r, e, hSurj, hInj, hFact, _hExact⟩ :=
    exists_tuple_equality_pattern_exact x
  refine ⟨m, r, hSurj, e, hInj, hFact, ?_⟩
  change Function.Injective e ∧
    (A.func F (e ∘ r)).Nonempty
  refine ⟨hInj, ?_⟩
  have heq : e ∘ r = x := by
    funext i
    exact (hFact i).symm
  rw [heq]
  exact hx


namespace Embedding

variable {W : Type v} {A : Structure L V} {B : Structure L W}

/-- Reflection of membership in a named complete source function
fibre follows from full fibre equality and injectivity. -/
theorem patternFibre_mem_iff
    (e : Embedding A B) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) (y : V) :
    e y ∈ B.func F (e ∘ x) ↔ y ∈ A.func F x := by
  constructor
  · intro hy
    rw [← e.map_func F x] at hy
    obtain ⟨z, hz, heq⟩ := hy
    have hzy : z = y := e.injective heq
    rwa [hzy] at hz
  · intro hy
    rw [← e.map_func F x]
    exact ⟨y, hy, rfl⟩

/-- Full primitive-function embeddings lift to induced relational
embeddings of the equality-pattern domain-and-graph language.
In particular, output reflection is not weakened to inclusion
of function graphs. -/
def patternGraph (e : Embedding A B) :
    RelStructure.Embedding A.patternGraph B.patternGraph where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | P
    · exact e.map_rel_iff R xs
    · rcases P with pat | pat
      · let args : Fin (L.funcArity pat.symbol) → V :=
          xs ∘ pat.argMap
        have hInj : Function.Injective (e ∘ xs) ↔
            Function.Injective xs := by
          constructor
          · intro he i j hij
            exact he (congrArg e hij)
          · intro hx i j hij
            exact hx (e.injective hij)
        have hDom :
            (B.func pat.symbol (e ∘ args)).Nonempty ↔
              (A.func pat.symbol args).Nonempty := by
          constructor
          · rintro ⟨z, hz⟩
            rw [← e.map_func pat.symbol args] at hz
            obtain ⟨y, hy, _⟩ := hz
            exact ⟨y, hy⟩
          · rintro ⟨y, hy⟩
            refine ⟨e y, ?_⟩
            rw [← e.map_func pat.symbol args]
            exact ⟨y, hy, rfl⟩
        change
          (Function.Injective (e ∘ xs) ∧
            (B.func pat.symbol (e ∘ args)).Nonempty) ↔
          (Function.Injective xs ∧
            (A.func pat.symbol args).Nonempty)
        exact and_congr hInj hDom
      · let root : Fin pat.rootSize → V :=
          fun i => xs (Fin.castSucc i)
        let args : Fin (L.funcArity pat.symbol) → V :=
          root ∘ pat.argMap
        let output : V := xs (Fin.last pat.rootSize)
        have hInj : Function.Injective (e ∘ root) ↔
            Function.Injective root := by
          constructor
          · intro he i j hij
            exact he (congrArg e hij)
          · intro hx i j hij
            exact hx (e.injective hij)
        have hVal :
            e output ∈ B.func pat.symbol (e ∘ args) ↔
              output ∈ A.func pat.symbol args :=
          e.patternFibre_mem_iff pat.symbol args output
        change
          (Function.Injective (e ∘ root) ∧
            e output ∈ B.func pat.symbol (e ∘ args)) ↔
          (Function.Injective root ∧
            output ∈ A.func pat.symbol args)
        exact and_congr hInj hVal

end Embedding

end Structure
end StructuralRamsey

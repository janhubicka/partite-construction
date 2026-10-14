import PartiteConstruction.Functional.PartialFunctionPatternGraph2019

/-!
# Decode exact equality-pattern relation records into set-valued functions

An arbitrary pattern-indexed relational structure may have incompatible
domain and graph tuples, so its raw relation reduct is not necessarily a
well-formed 2019 functional closure encoding.

For the canonical expansion of a finite genuine function structure,
the decoder recovers every original fibre exactly, including full
multivalued fibres and repeated input arguments. A decoded value is
witnessed by BOTH the corresponding canonical domain tuple and its
actual output-graph tuple on an injective enumeration of the exact
distinct input vertices.

This establishes the pointwise canonical round trip. It does NOT
assert the converse for arbitrary pattern-relational structures;
future closure-tag normality and validity lemmas must establish
that their domain and graph records are coherent.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Decode all pattern-indexed output tuples on the original vertex set.
We insist on the domain relation as well as the output incidence,
so inconsistent relational targets do not create unannounced function
domains from stray output-graph tuples. -/
def patternDecode (E : RelStructure (L.patternGraph) V) :
    Structure L V where
  rel R x := E.rel (.inl R) x
  func F x := {y | ∃ (m : ℕ)
      (r : Fin (L.funcArity F) → Fin m)
      (hr : Function.Surjective r)
      (root : Fin m → V),
      Function.Injective root ∧
      (∀ i, x i = root (r i)) ∧
      E.rel (.inr (.inl
        ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
          Language.FunctionInputPattern L))) root ∧
      E.rel (.inr (.inr
        ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
          Language.FunctionInputPattern L)))
        (funcTuple root y)}

/-- Original relations are reproduced definitionally by decoding a
canonical pattern graph. -/
theorem patternDecode_patternGraph_rel
    (A : Structure L V)
    (R : L.RelSymbol) (x : Fin (L.relArity R) → V) :
    (patternDecode A.patternGraph).rel R x ↔ A.rel R x :=
  Iff.rfl

/-- Every original function fibre, including a *multivalued* fibre,
is recovered by the pattern decoder on the same original vertex set.
No closure of the source inputs is inserted. -/
theorem patternDecode_patternGraph_func
    (A : Structure L V) [Finite V]
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) (y : V) :
    y ∈ (patternDecode A.patternGraph).func F x ↔
      y ∈ A.func F x := by
  classical
  constructor
  · rintro ⟨m, r, hr, root, hinj, hfact, _hdom, hgraph⟩
    change Function.Injective
        (fun i : Fin m => (funcTuple root y) i.castSucc) ∧
      (funcTuple root y) (Fin.last m) ∈
        A.func F
          ((fun i : Fin m => (funcTuple root y) i.castSucc) ∘ r) at hgraph
    have hroot : root ∘ r = x := by
      funext i
      exact (hfact i).symm
    simpa [funcTuple_castSucc, funcTuple_last, hroot] using hgraph.2
  · intro hy
    obtain ⟨m, r, root, hr, hinj, hfact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact x
    refine ⟨m, r, hr, root, hinj, hfact, ?_, ?_⟩
    · change Function.Injective root ∧
        (A.func F (root ∘ r)).Nonempty
      refine ⟨hinj, ?_⟩
      have hx : root ∘ r = x := by
        funext i
        exact (hfact i).symm
      rw [hx]
      exact ⟨y, hy⟩
    · change Function.Injective
          (fun i : Fin m => (funcTuple root y) i.castSucc) ∧
        (funcTuple root y) (Fin.last m) ∈
          A.func F
            ((fun i : Fin m => (funcTuple root y) i.castSucc) ∘ r)
      constructor
      · simpa using hinj
      · have hx : root ∘ r = x := by
          funext i
          exact (hfact i).symm
        simpa [funcTuple_castSucc, funcTuple_last, hx] using hy

end StructuralRamsey.Structure

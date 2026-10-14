import PartiteConstruction.Functional.PartialFunctionPatternDecode2019

/-!
# Decoded OLD function outputs are preserved by induced graph embeddings

An embedding of OLD equality-pattern relation structures into a
canonical primitive-function graph is automatically POSITIVE on
the decoded native set-valued function fibres. The proof uses the
actual graph tuple witnessing membership, reconstructs the original
possibly repeated arguments, and invokes the full induced
preservation of that graph tuple.

Unlike a primitive full function embedding, this positive map need
not reflect empty function domains or extra target fibre elements.
Those properties follow later only under the protected closure
coverage and singleton-valuedness hypotheses.
-/

namespace StructuralRamsey.RelStructure.Embedding

open StructuralRamsey

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {E : RelStructure (L.patternGraph) V}
variable {Base : Structure L W}

/-- Every OLD decoded output survives any full embedding of the
OLD pattern graph into the canonical pattern graph of Base. This
requires no closure or singleton-valuedness assumptions. -/
theorem map_patternDecode_func
    (e : Embedding E Base.patternGraph)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) (y : V)
    (hy : y ∈ (Structure.patternDecode E).func F x) :
    e y ∈ Base.func F (e ∘ x) := by
  obtain ⟨m, r, hr, root, _hInj, hFact, _hDom, hGraph⟩ := hy
  let p : Language.FunctionInputPattern L := {
    symbol := F
    rootSize := m
    argMap := r
    onto := hr
  }
  have hTarget : Base.patternGraph.rel (.inr (.inr p))
      (e ∘ Structure.funcTuple root y) :=
    (e.map_rel_iff (.inr (.inr p))
      (Structure.funcTuple root y)).mpr hGraph
  have hTuple := Structure.comp_funcTuple e root y
  rw [hTuple] at hTarget
  have hGraphTarget :
      Function.Injective (e ∘ root) ∧
        e y ∈ Base.func F ((e ∘ root) ∘ r) := hTarget
  have hArgs : (e ∘ root) ∘ r = e ∘ x := by
    funext i
    exact congrArg e (hFact i).symm
  rw [hArgs] at hGraphTarget
  exact hGraphTarget.2

end StructuralRamsey.RelStructure.Embedding

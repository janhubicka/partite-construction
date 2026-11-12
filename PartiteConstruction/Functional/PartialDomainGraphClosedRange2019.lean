import PartiteConstruction.Functional.PartialDomainGraphFullEmbedding2019

/-!
# Track A: graph embeddings plus function-closed images are precisely full
# genuine partial-function embeddings

A full `Option (Set V)` functional embedding has a function-closed range.
Conversely, an induced embedding of the separate domain/output relational
encoding with a function-closed range cannot create additional function
outputs over any source-defined input: closure places each target output in
the image, and inducedness reflects its positive output incidence.

This yields a geometric replacement of the exact-fibre-surjectivity
hypothesis in the previous full-embedding dictionary. All constructions are
on the literal same source and target carriers and vertex map; they impose
no positivity-of-arity, finiteness, transversality, irreducibility, or
generator-hull assumption. Defined-empty is distinguished from undefined.

The result is a source/map theorem, not a U-closed local-completion
hypothesis or a strict functional mixed-root B-tree construction.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {A : PartialSetStructure L V} {B : PartialSetStructure L W}

namespace Embedding

/-- Full partial-function embeddings have function-closed ranges.
Importantly, the closure statement includes nullary operations and
genuinely defined-empty inputs. -/
theorem range_isClosed (e : Embedding A B) :
    B.IsClosed (Set.range e.toFun) := by
  classical
  intro F ys T hArgs hT y hy
  let xs : Fin (L.funcArity F) → V :=
    fun i => Classical.choose (hArgs i)
  have hxs : e.toFun ∘ xs = ys := by
    funext i
    exact Classical.choose_spec (hArgs i)
  have hTargetDefined : B.Defined F (e.toFun ∘ xs) := by
    refine ⟨T, ?_⟩
    rw [hxs]
    exact hT
  have hSourceDefined : A.Defined F xs := by
    exact (e.domainGraph.map_rel_iff (.inr (.inl F)) xs).mp
      hTargetDefined
  obtain ⟨U, hU⟩ := hSourceDefined
  have hOutput : B.HasOutput F (e.toFun ∘ xs) y := by
    refine ⟨T, ?_, hy⟩
    rw [hxs]
    exact hT
  obtain ⟨z, _hz, heq⟩ :=
    e.noExtraTargetOutputsOnDefined F xs U hU y hOutput
  exact ⟨z, heq⟩

end Embedding

/-- An induced domain/output-graph embedding together with a
function-closed target range maps every source-defined complete
function fibre ONTO the corresponding target fibre. -/
theorem noExtra_of_domainGraphEmbedding_closed
    (g : RelStructure.Embedding
      (PartialSetStructure.domainGraph A)
      (PartialSetStructure.domainGraph B))
    (hClosed : B.IsClosed (Set.range g.toFun)) :
    NoExtraTargetOutputsOnDefined A B g.toFun := by
  intro F xs U hU y hy
  obtain ⟨T, hT, hyT⟩ := hy
  have hArgs : ∀ i : Fin (L.funcArity F),
      (g.toFun ∘ xs) i ∈ Set.range g.toFun := by
    intro i
    exact ⟨xs i, rfl⟩
  have hRange : y ∈ Set.range g.toFun :=
    hClosed F (g.toFun ∘ xs) T hArgs hT hyT
  obtain ⟨z, hzy⟩ := hRange
  have hOutB :
      (PartialSetStructure.domainGraph B).rel (.inr (.inr F))
        (Structure.funcTuple (g.toFun ∘ xs) (g.toFun z)) := by
    have hAt : B.HasOutput F (g.toFun ∘ xs) (g.toFun z) := by
      refine ⟨T, hT, ?_⟩
      rw [hzy]
      exact hyT
    simpa only [domainGraph, Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using hAt
  have hOutB' :
      (PartialSetStructure.domainGraph B).rel (.inr (.inr F))
        (g.toFun ∘ Structure.funcTuple xs z) := by
    have hTuple : g.toFun ∘ Structure.funcTuple xs z =
        Structure.funcTuple (g.toFun ∘ xs) (g.toFun z) :=
      Structure.comp_funcTuple g.toFun xs z
    exact hTuple.symm ▸ hOutB
  have hOutA :
      (PartialSetStructure.domainGraph A).rel (.inr (.inr F))
        (Structure.funcTuple xs z) :=
    (g.map_rel_iff (.inr (.inr F)) (Structure.funcTuple xs z)).mp hOutB'
  have hSourceOutput : A.HasOutput F xs z := by
    simpa only [domainGraph, Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using hOutA
  obtain ⟨U', hU', hzU'⟩ := hSourceOutput
  have hUU' : U' = U :=
    Option.some.inj (hU'.symm.trans hU)
  have hzU : z ∈ U := by
    simpa only [hUU'] using hzU'
  exact ⟨z, hzU, hzy⟩

/-- For an induced embedding of the two-relation domain/output graph,
the exact output-fibre condition is EQUIVALENT to function-closedness
of its actual target vertex image. Neither condition demands that
source-undefined applications remain undefined without the graph
embedding's domain-reflection hypothesis. -/
theorem noExtra_iff_closedRange_of_domainGraphEmbedding
    (g : RelStructure.Embedding
      (PartialSetStructure.domainGraph A)
      (PartialSetStructure.domainGraph B)) :
    NoExtraTargetOutputsOnDefined A B g.toFun ↔
      B.IsClosed (Set.range g.toFun) := by
  constructor
  · intro hExtra
    exact (Embedding.ofDomainGraphNoExtra g hExtra).range_isClosed
  · exact noExtra_of_domainGraphEmbedding_closed g

/-- Exact full-embedding dictionary in terms of the familiar geometric
notion of a function-closed image. The relational embedding must encode
BOTH independent domain and output relations; an output-only graph
embedding loses the defined-empty/undefined distinction. -/
theorem fullEmbedding_iff_domainGraphEmbedding_closedRange
    (A : PartialSetStructure L V)
    (B : PartialSetStructure L W) (f : V → W) :
    (∃ e : Embedding A B, e.toFun = f) ↔
      (∃ g : RelStructure.Embedding
        (PartialSetStructure.domainGraph A)
        (PartialSetStructure.domainGraph B), g.toFun = f) ∧
      B.IsClosed (Set.range f) := by
  constructor
  · rintro ⟨e, he⟩
    subst f
    exact ⟨⟨e.domainGraph, rfl⟩, e.range_isClosed⟩
  · rintro ⟨⟨g, hg⟩, hClosed⟩
    subst f
    have hExtra : NoExtraTargetOutputsOnDefined A B g.toFun :=
      (noExtra_iff_closedRange_of_domainGraphEmbedding g).mpr hClosed
    exact ⟨Embedding.ofDomainGraphNoExtra g hExtra, rfl⟩

end StructuralRamsey.PartialSetStructure

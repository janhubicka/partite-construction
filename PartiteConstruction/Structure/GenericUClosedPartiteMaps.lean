import PartiteConstruction.Structure.GenericUOutputTransversal
import PartiteConstruction.Structure.GenericUCombinedClosureBridge
import PartiteConstruction.Functional.Closed

/-!
# Exact source-fibre/partite-embedding U-closedness under generic U-reindex

The printed Appendix A lemmas use induced PARTITE embeddings whose ranges
are closed under the last outputs of each distinguished original relation.
The established function-graph lemmas use FunctionClosedMap instead.
This module proves the predicates agree for the same vertex injection
and part map; it neither adds a closure hull nor imposes singleton fibres.

The full partite Ramsey-arrow equivalence remains a separate obligation.
-/

namespace StructuralRamsey
universe u v

namespace Partite.Embedding

variable {L : RelLanguage.{u}} {P V W : Type v}
variable {A : Partite.System L P V} {B : Partite.System L P W}

/-- The ORIGINAL closed-range condition for a partite embedding agrees
with function-output lifting in its reindexed graph, on the same map. -/
theorem uClosedRange_iff_functionClosedMap
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Partite.Embedding A B) :
    RelStructure.IsUClosedEmbeddingRange U hU e.toEmbedding ↔
      RelStructure.FunctionClosedMap
        (A.asReducedUGraph U hU).toRelStructure
        (B.asReducedUGraph U hU).toRelStructure
        e.toEmbedding.toFun := by
  constructor
  · intro hr F x y hy
    have hlift : RelStructure.IsUClosedEmbedding
        A.toRelStructure B.toRelStructure U hU e.toEmbedding :=
      (RelStructure.isUClosedEmbedding_iff_range U hU e.toEmbedding).mpr hr
    have ht : B.rel F.1
        (RelLanguage.appendU L U hU F (e.toEmbedding.toFun ∘ x) y) :=
      (B.reducedUGraph_func_snoc_iff U hU F
        (e.toEmbedding.toFun ∘ x) y).mp hy
    obtain ⟨z, hz, hzy⟩ := hlift F x y ht
    exact ⟨z, (A.reducedUGraph_func_snoc_iff U hU F x z).mpr hz, hzy⟩
  · intro hg
    apply (RelStructure.isUClosedEmbedding_iff_range U hU e.toEmbedding).mp
    intro F x y hy
    have ht : (B.asReducedUGraph U hU).rel (.inr F)
        (Structure.funcTuple (e.toEmbedding.toFun ∘ x) y) :=
      (B.reducedUGraph_func_snoc_iff U hU F
        (e.toEmbedding.toFun ∘ x) y).mpr hy
    obtain ⟨z, hz, hzy⟩ := hg F x y ht
    exact ⟨z, (A.reducedUGraph_func_snoc_iff U hU F x z).mp hz, hzy⟩

/-- Every original U-closed partite embedding gives a closed embedding of
the graph relational structures on the IDENTICAL underlying vertex map. -/
noncomputable def toGraphClosed
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Partite.Embedding A B)
    (he : RelStructure.IsUClosedEmbeddingRange U hU e.toEmbedding) :
    RelStructure.ClosedEmbedding
      (A.asReducedUGraph U hU).toRelStructure
      (B.asReducedUGraph U hU).toRelStructure where
  toEmbedding := e.toEmbedding.asReducedUGraph U hU
  closed := (uClosedRange_iff_functionClosedMap U hU e).mp he

@[simp] theorem toGraphClosed_apply
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Partite.Embedding A B)
    (he : RelStructure.IsUClosedEmbeddingRange U hU e.toEmbedding)
    (x : V) :
    toGraphClosed U hU e he x = e x := rfl

end Partite.Embedding
end StructuralRamsey

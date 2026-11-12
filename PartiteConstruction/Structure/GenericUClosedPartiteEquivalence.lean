import PartiteConstruction.Structure.GenericUClosedPartiteMaps
import PartiteConstruction.Structure.GenericUGraphPartiteInverse
import PartiteConstruction.Structure.GenericUGraphInverse
import PartiteConstruction.Functional.ClosedPartite

/-!
# Track F — full same-map closed partite embedding dictionary

The printed original arbitrary relational (L,U) partite lemma colours
induced PARTITE embeddings with U-closed ranges. The function-graph partite
lemma colours graph-partite embeddings with exact function-fibre lifting.

Both conditions identify exactly the same underlying injection and part
map after nonredundant U-reindexing; the reverse direction requires genuine
relation reflection, not just positive homomorphism preservation.

No Ramsey statement, finiteness, irreducibility of B, B-closedness, or
function-singleton assumption is introduced by this dictionary.
-/

namespace StructuralRamsey.Partite

universe u v

namespace Embedding

variable {L : RelLanguage.{u}} {P V W : Type v}
variable {A : Partite.System L P V} {B : Partite.System L P W}

/-- Recover an ORIGINAL part-preserving induced embedding from an induced
embedding between the two exact U-reindexed graph partite systems.
The underlying vertex injection is unchanged, with no closure assumption. -/
noncomputable def ofReindexed
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (f : Partite.Embedding
      (A.asReducedUGraph U hU) (B.asReducedUGraph U hU)) :
    Partite.Embedding A B where
  toEmbedding := {
    toFun := f.toEmbedding
    injective := f.toEmbedding.injective
    map_rel_iff := by
      intro R t
      let ef := RelStructure.Embedding.fromReducedUGraph
        U hU f.toEmbedding
      calc
        B.rel R (f.toEmbedding.toFun ∘ t) ↔
          (RelStructure.fromReducedUGraph U hU
            (B.toRelStructure.asReducedUGraph U hU)).rel R
              (f.toEmbedding.toFun ∘ t) :=
            (RelStructure.from_asReducedUGraph_rel_iff
              B.toRelStructure U hU R (f.toEmbedding.toFun ∘ t)).symm
        _ ↔ (RelStructure.fromReducedUGraph U hU
            (A.toRelStructure.asReducedUGraph U hU)).rel R t :=
          ef.map_rel_iff R t
        _ ↔ A.rel R t :=
          RelStructure.from_asReducedUGraph_rel_iff
            A.toRelStructure U hU R t
  }
  map_part := f.map_part

@[simp] theorem ofReindexed_apply
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (f : Partite.Embedding
      (A.asReducedUGraph U hU) (B.asReducedUGraph U hU))
    (x : V) :
    (ofReindexed U hU f) x = f x := rfl

/-- Exact equivalence of the *closed partite embedding types* in the
original language and in the graph of its nonredundant U-function encoding.
Every source and target map is literally the same injection. -/
noncomputable def uClosedReindexEquiv
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    {e : Partite.Embedding A B //
       RelStructure.IsUClosedEmbeddingRange U hU e.toEmbedding} ≃
      Partite.Closed.Embedding
        (A.asReducedUGraph U hU) (B.asReducedUGraph U hU) where
  toFun e := ⟨e.1.asReducedUGraph U hU,
    (uClosedRange_iff_functionClosedMap U hU e.1).mp e.2⟩
  invFun g := by
    let e := ofReindexed U hU g.1
    have hgraph : RelStructure.FunctionClosedMap
        (A.asReducedUGraph U hU).toRelStructure
        (B.asReducedUGraph U hU).toRelStructure
        e.toEmbedding.toFun := by
      exact g.2
    exact ⟨e, (uClosedRange_iff_functionClosedMap U hU e).mpr hgraph⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Partite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro g
    apply Partite.Closed.Embedding.ext
    intro x
    rfl

@[simp] theorem uClosedReindexEquiv_apply
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : {e : Partite.Embedding A B //
       RelStructure.IsUClosedEmbeddingRange U hU e.toEmbedding})
    (x : V) :
    (uClosedReindexEquiv U hU e) x = e.1 x := rfl

end Embedding
end StructuralRamsey.Partite

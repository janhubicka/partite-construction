import PartiteConstruction.Structure.GenericUGraphPartiteInverse
import PartiteConstruction.Structure.GenericUGraphInverse
import PartiteConstruction.Functional.ClosedPicture

/-!
# Track F — arbitrary graph Picture witnesses survive original-language roundtrip

The verified function-graph Picture lemma returns an arbitrary graph-language
partite witness C, rather than an original-encoded C.  The nonredundant
U-signature has no separate coherence condition: decoding C to original L and
encoding it back yields the same graph relation on the same vertex and part
maps.  We package the identity on vertices into genuinely function-closed
partite embeddings in BOTH directions.

The last equivalence transports the exact projected closed A-copies needed
for colouring in the Picture lemma, including their prescribed part map.
These contracts do not yet establish the full original Picture arrow.
-/

namespace StructuralRamsey.Partite
universe u v

namespace System

variable {L : RelLanguage.{u}} {P V : Type v}

/-- An arbitrary graph-partite witness is closed-isomorphic, on the
literal identity vertex map, to its original-U decode and re-encode. -/
noncomputable def graphRoundtripClosedForward
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V) :
    Partite.Closed.Embedding
      ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph U hU)
      B := by
  let C := (Partite.System.fromReducedUGraph U hU B).asReducedUGraph U hU
  let eR : RelStructure.Embedding C.toRelStructure B.toRelStructure := {
    toFun := id
    injective := by intro x y h; exact h
    map_rel_iff := by
      intro S t
      exact (RelStructure.as_fromReducedUGraph_rel_iff
        U hU B.toRelStructure S t).symm
  }
  let eP : Partite.Embedding C B := {
    toEmbedding := eR
    map_part := by intro x; rfl
  }
  refine ⟨eP, ?_⟩
  intro F x y hy
  refine ⟨y, ?_, rfl⟩
  exact (RelStructure.as_fromReducedUGraph_rel_iff
    U hU B.toRelStructure (.inr F) (Structure.funcTuple x y)).mpr hy

/-- The inverse closed embedding is again literally the identity map. -/
noncomputable def graphRoundtripClosedBackward
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V) :
    Partite.Closed.Embedding
      B
      ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph U hU) := by
  let C := (Partite.System.fromReducedUGraph U hU B).asReducedUGraph U hU
  let eR : RelStructure.Embedding B.toRelStructure C.toRelStructure := {
    toFun := id
    injective := by intro x y h; exact h
    map_rel_iff := by
      intro S t
      exact RelStructure.as_fromReducedUGraph_rel_iff
        U hU B.toRelStructure S t
  }
  let eP : Partite.Embedding B C := {
    toEmbedding := eR
    map_part := by intro x; rfl
  }
  refine ⟨eP, ?_⟩
  intro F x y hy
  refine ⟨y, ?_, rfl⟩
  exact (RelStructure.as_fromReducedUGraph_rel_iff
    U hU B.toRelStructure (.inr F) (Structure.funcTuple x y)).mp hy

end System

namespace Closed

variable {L : RelLanguage.{u}} {P T V : Type v}

/-- Closed projected A-copies of an arbitrary graph Picture witness are
identical, including their alpha projection, after decoding to original L
and re-encoding to the graph language.  Neither direction introduces a
new vertex, a coherence premise or an arity restriction beyond positivity. -/
noncomputable def projectedRoundtripEquiv
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (A : RelStructure (L.withUFunctionsReduced U).graph T)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V)
    (α : T → P) :
    Partite.Closed.ProjectedEmbedding A B α ≃
      Partite.Closed.ProjectedEmbedding A
        ((Partite.System.fromReducedUGraph U hU B).asReducedUGraph U hU)
        α where
  toFun e := e.comp (Partite.System.graphRoundtripClosedBackward U hU B)
  invFun e := e.comp (Partite.System.graphRoundtripClosedForward U hU B)
  left_inv := by
    intro e
    apply Partite.Closed.ProjectedEmbedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Partite.Closed.ProjectedEmbedding.ext
    intro x
    rfl

end Closed
end StructuralRamsey.Partite

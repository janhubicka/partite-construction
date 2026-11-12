import PartiteConstruction.Structure.GenericUGraphPartite

/-!
# Inverse partite-system reindexing from the U-function graph to original L

The translated graph signature has exactly one symbol for every original
relation of L. Every graph structure is therefore decoded by direct symbol
and tuple reindexing, WITHOUT a coherence hypothesis or a new vertex.

This module transports the actual partite system and part-preserving
induced embeddings back to the original arbitrary (L,U) language. In
particular, named part maps and repeated tuple entries are unchanged.
-/

namespace StructuralRamsey

universe u v w z

namespace RelStructure.Embedding

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Backward transport of induced relational embeddings through the
nonredundant U-graph symbol equivalence. Its underlying injection is
exactly the original embedding map. -/
noncomputable def fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure (L.withUFunctionsReduced U).graph V}
    {B : RelStructure (L.withUFunctionsReduced U).graph W}
    (e : Embedding A B) :
    Embedding (RelStructure.fromReducedUGraph U hU A)
      (RelStructure.fromReducedUGraph U hU B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R t
    exact e.map_rel_iff (L.toReducedUGraphSymbol U R)
      (fun i => t (Fin.cast
        (L.reducedUGraphSymbol_arity U hU R) i))

@[simp] theorem fromReducedUGraph_apply
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure (L.withUFunctionsReduced U).graph V}
    {B : RelStructure (L.withUFunctionsReduced U).graph W}
    (e : Embedding A B) (x : V) :
    (e.fromReducedUGraph U hU) x = e x := rfl

@[simp] theorem fromReducedUGraph_comp
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure (L.withUFunctionsReduced U).graph V}
    {B : RelStructure (L.withUFunctionsReduced U).graph W}
    {X : Type z}
    {C : RelStructure (L.withUFunctionsReduced U).graph X}
    (f : Embedding B C) (e : Embedding A B) :
    (f.comp e).fromReducedUGraph U hU =
      (f.fromReducedUGraph U hU).comp (e.fromReducedUGraph U hU) := by
  apply Embedding.ext
  intro x
  rfl

end RelStructure.Embedding

namespace Partite.System

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- Decode a graph-language partite system on the exact same vertices,
parts and projection map, using the inverse symbol/arity equivalence. -/
noncomputable def fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V) :
    Partite.System L P V where
  toRelStructure := RelStructure.fromReducedUGraph U hU B.toRelStructure
  part := B.part
  transversal := by
    intro R t ht i j hp
    let S := L.toReducedUGraphSymbol U R
    let hR := L.reducedUGraphSymbol_arity U hU R
    let t' : Fin ((L.withUFunctionsReduced U).graph.arity S) → V :=
      fun k => t (Fin.cast hR k)
    have ht' : B.rel S t' := ht
    have hi : t' (Fin.cast hR.symm i) = t i := by
      change t (Fin.cast hR (Fin.cast hR.symm i)) = t i
      have hc : Fin.cast hR (Fin.cast hR.symm i) = i := Fin.ext rfl
      exact congrArg t hc
    have hj : t' (Fin.cast hR.symm j) = t j := by
      change t (Fin.cast hR (Fin.cast hR.symm j)) = t j
      have hc : Fin.cast hR (Fin.cast hR.symm j) = j := Fin.ext rfl
      exact congrArg t hc
    have hp' :
        B.part (t' (Fin.cast hR.symm i)) =
          B.part (t' (Fin.cast hR.symm j)) := by
      simpa only [hi, hj] using hp
    have he := B.transversal S t' ht'
      (Fin.cast hR.symm i) (Fin.cast hR.symm j) hp'
    exact hi.symm.trans (he.trans hj)

@[simp] theorem fromReducedUGraph_part
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V)
    (x : V) :
    (B.fromReducedUGraph U hU).part x = B.part x := rfl

/-- The original-language partite relation is exactly the corresponding
decoded graph relation (same tuple, modulo the canonical arity cast). -/
theorem fromReducedUGraph_rel_iff
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V)
    (R : L.Symbol) (t : Fin (L.arity R) → V) :
    (B.fromReducedUGraph U hU).rel R t ↔
      B.rel (L.toReducedUGraphSymbol U R)
        (fun i => t (Fin.cast
          (L.reducedUGraphSymbol_arity U hU R) i)) :=
  Iff.rfl

end Partite.System

namespace Partite.Embedding

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {W : Type z}

/-- Part-preserving full embeddings also decode directly, retaining the
entire part map and the genuine induced relational embedding data. -/
noncomputable def fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : Partite.System (L.withUFunctionsReduced U).graph P V}
    {B : Partite.System (L.withUFunctionsReduced U).graph P W}
    (e : Partite.Embedding A B) :
    Partite.Embedding
      (Partite.System.fromReducedUGraph U hU A)
      (Partite.System.fromReducedUGraph U hU B) where
  toEmbedding := e.toEmbedding.fromReducedUGraph U hU
  map_part := e.map_part

@[simp] theorem fromReducedUGraph_apply
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : Partite.System (L.withUFunctionsReduced U).graph P V}
    {B : Partite.System (L.withUFunctionsReduced U).graph P W}
    (e : Partite.Embedding A B) (x : V) :
    (e.fromReducedUGraph U hU) x = e x := rfl

end Partite.Embedding
end StructuralRamsey

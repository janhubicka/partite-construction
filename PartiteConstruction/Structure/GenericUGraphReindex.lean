import PartiteConstruction.Structure.GenericUGraphSymbols
import PartiteConstruction.Partite.Basic

/-!
# Reindex arbitrary L-relations into the graph language of U-functions

This uses the actual arity-preserving symbol equivalence from Track F #584.
All vertex sets and tuples remain unchanged up to Fin.cast, including nullary
non-U relations, repeated coordinates, and empty output fibres.

The reindexing below is purely structural and does not require closure or a
Ramsey hypothesis. It is designed to be compared with the actual graph of
the nonredundant set-valued-function encoding in a separate theorem.
-/

namespace StructuralRamsey

universe u v w

namespace RelLanguage

/-- The inverse symbol direction preserves the corresponding arities. -/
theorem reducedUGraphSymbol_arity_from
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : (L.withUFunctionsReduced U).graph.Symbol) :
    L.arity (L.fromReducedUGraphSymbol U S) =
      (L.withUFunctionsReduced U).graph.arity S := by
  have h := L.reducedUGraphSymbol_arity U hU
    (L.fromReducedUGraphSymbol U S)
  rw [L.to_fromReducedUGraphSymbol U S] at h
  exact h.symm

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Reindex a relational structure along the inverse of the symbol
equivalence, retaining the EXACT same carrier and relations. -/
noncomputable def asReducedUGraph
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    RelStructure (L.withUFunctionsReduced U).graph V where
  rel S t := A.rel (L.fromReducedUGraphSymbol U S)
    (fun i => t (Fin.cast (L.reducedUGraphSymbol_arity_from U hU S) i))

/-- Reindex a graph-language structure into the original relational
signature on the same carrier, without constructing any closure hull. -/
noncomputable def fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.withUFunctionsReduced U).graph V) :
    RelStructure L V where
  rel R t := D.rel (L.toReducedUGraphSymbol U R)
    (fun i => t (Fin.cast (L.reducedUGraphSymbol_arity U hU R) i))

/-- Direct, full relation-membership interpretation of the source reindex. -/
theorem asReducedUGraph_rel_iff
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) → V) :
    (A.asReducedUGraph U hU).rel S t ↔
      A.rel (L.fromReducedUGraphSymbol U S)
        (fun i => t (Fin.cast
          (L.reducedUGraphSymbol_arity_from U hU S) i)) :=
  Iff.rfl

/-- The inverse pullback has exactly the relation indicated by the
symbol equivalence and the arity cast. -/
theorem fromReducedUGraph_rel_iff
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.withUFunctionsReduced U).graph V)
    (R : L.Symbol) (t : Fin (L.arity R) → V) :
    (fromReducedUGraph U hU D).rel R t ↔
      D.rel (L.toReducedUGraphSymbol U R)
        (fun i => t (Fin.cast
          (L.reducedUGraphSymbol_arity U hU R) i)) :=
  Iff.rfl

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W}

/-- An induced embedding remains an induced embedding after exact language
reindexing. The underlying injection does not change. -/
noncomputable def asReducedUGraph
    (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    Embedding (A.asReducedUGraph U hU) (B.asReducedUGraph U hU) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro S t
    change B.rel (L.fromReducedUGraphSymbol U S)
      (e.toFun ∘ (fun i =>
        t (Fin.cast (L.reducedUGraphSymbol_arity_from U hU S) i))) ↔
      A.rel (L.fromReducedUGraphSymbol U S)
      (fun i => t (Fin.cast
        (L.reducedUGraphSymbol_arity_from U hU S) i))
    exact e.map_rel_iff (L.fromReducedUGraphSymbol U S) _

@[simp] theorem asReducedUGraph_apply
    (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) (x : V) :
    (e.asReducedUGraph U hU) x = e x := rfl

@[simp] theorem asReducedUGraph_comp
    {X : Type*} {C : RelStructure L X}
    (f : Embedding B C) (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (f.comp e).asReducedUGraph U hU =
      (f.asReducedUGraph U hU).comp (e.asReducedUGraph U hU) := by
  apply Embedding.ext
  intro x
  rfl

end Embedding
end RelStructure
end StructuralRamsey

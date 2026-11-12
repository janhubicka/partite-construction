import PartiteConstruction.Structure.GenericUGraphPartite
import PartiteConstruction.Structure.Relationalize

/-!
# Semantics of arbitrary (L,U) reindexing versus the genuine function graph

Partite-system reindexing is not yet sufficient unless the reindexed relation
really coincides with the graph of the nonredundant set-valued U-encoding.
This file establishes the semantic link for every original relation tuple,
including repeated vertices, nullary non-U relations and empty U-fibres.

No closure, irreducibility, Ramsey or Picture assumption is used.
-/

namespace StructuralRamsey

universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v}

/-- Reindexing the original relations preserves exactly the same incidence
predicate as graph-encoding the U-functions, for every symbol and tuple. -/
theorem asReducedUGraph_iff_functionGraph
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) → V) :
    (A.asReducedUGraph U hU).rel S t ↔
      (A.asUFunctionsReduced U hU).graph.rel S t := by
  classical
  cases S with
  | inl R =>
      change A.rel R.1
        (fun i => t (Fin.cast
          (L.reducedUGraphSymbol_arity_from U hU (.inl R)) i)) ↔
        A.rel R.1 t
      have ht :
          (fun i : Fin (L.arity R.1) =>
            t (Fin.cast
              (L.reducedUGraphSymbol_arity_from U hU (.inl R)) i))
            = t := by
        funext i
        congr 1
        exact Fin.ext rfl
      rw [ht]
  | inr F =>
      let q : Fin (L.arity F.1) → V := fun i =>
        t (Fin.cast (L.reducedUGraphSymbol_arity_from U hU (.inr F)) i)
      have hq :
          q = RelLanguage.appendU L U hU F
            (fun i => t i.castSucc)
            (t (Fin.last (L.arity F.1 - 1))) := by
        funext i
        change t (Fin.cast
          (L.reducedUGraphSymbol_arity_from U hU (.inr F)) i) =
          Structure.funcTuple
            (fun j => t j.castSucc)
            (t (Fin.last (L.arity F.1 - 1)))
            (Fin.cast ((Nat.sub_add_cancel (hU F.1 F.2)).symm) i)
        rw [Structure.funcTuple_eta t]
        congr 1
        exact Fin.ext rfl
      change A.rel F.1 q ↔
        A.rel F.1 (RelLanguage.appendU L U hU F
          (fun i => t i.castSucc)
          (t (Fin.last (L.arity F.1 - 1))))
      rw [hq]

end RelStructure

namespace Partite.System

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- The exact partite reindex has the same relation as the genuine
set-valued-function graph, not just an abstract language isomorphism. -/
theorem asReducedUGraph_iff_functionGraph
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) → V) :
    (B.asReducedUGraph U hU).rel S t ↔
      (B.toRelStructure.asUFunctionsReduced U hU).graph.rel S t :=
  RelStructure.asReducedUGraph_iff_functionGraph B.toRelStructure U hU S t

end Partite.System
end StructuralRamsey

import PartiteConstruction.Structure.GenericUGraphPartite
import PartiteConstruction.Relational.Homomorphism

/-!
# Inverse generic graph reindex and homomorphism preservation

The original and reduced-function-graph signatures have a genuine symbol
equivalence and matching arities. This module verifies that reindexing on
an unchanged vertex carrier preserves every relational incidence, including
the round trip in both directions. It also transports positive relational
homomorphisms on the *same* underlying map.

These are intermediate contracts for transporting the partite projection
homomorphism-embedding. No Ramsey arrow is asserted here.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Reindexing from an arbitrary original L-structure into the graph language
and back reproduces every original relation on the same vertices. -/
theorem from_asReducedUGraph_rel_iff
    (A : RelStructure L V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (R : L.Symbol)
    (t : Fin (L.arity R) → V) :
    (fromReducedUGraph U hU (A.asReducedUGraph U hU)).rel R t ↔
      A.rel R t := by
  classical
  change A.rel (L.fromReducedUGraphSymbol U
    (L.toReducedUGraphSymbol U R))
    (fun i => t (Fin.cast (L.reducedUGraphSymbol_arity U hU R)
      (Fin.cast (L.reducedUGraphSymbol_arity_from U hU
        (L.toReducedUGraphSymbol U R)) i))) ↔ A.rel R t
  have hsym := L.from_toReducedUGraphSymbol U R
  cases hsym
  have ht :
      (fun i : Fin (L.arity R) =>
        t (Fin.cast (L.reducedUGraphSymbol_arity U hU R)
          (Fin.cast (L.reducedUGraphSymbol_arity_from U hU
            (L.toReducedUGraphSymbol U R)) i))) = t := by
    funext i
    exact congrArg t (Fin.ext rfl)
  simpa only [ht]

/-- Every arbitrary graph-language structure likewise survives the inverse
roundtrip; no coherence of its relations with a separate function symbol is
required, because the signature is nonredundant. -/
theorem as_fromReducedUGraph_rel_iff
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.withUFunctionsReduced U).graph V)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) → V) :
    ((fromReducedUGraph U hU D).asReducedUGraph U hU).rel S t ↔
      D.rel S t := by
  classical
  change D.rel (L.toReducedUGraphSymbol U
      (L.fromReducedUGraphSymbol U S))
    (fun i => t (Fin.cast (L.reducedUGraphSymbol_arity_from U hU S)
      (Fin.cast (L.reducedUGraphSymbol_arity U hU
        (L.fromReducedUGraphSymbol U S)) i))) ↔ D.rel S t
  have hsym := L.to_fromReducedUGraphSymbol U S
  cases hsym
  have ht :
      (fun i : Fin ((L.withUFunctionsReduced U).graph.arity S) =>
        t (Fin.cast (L.reducedUGraphSymbol_arity_from U hU S)
          (Fin.cast (L.reducedUGraphSymbol_arity U hU
            (L.fromReducedUGraphSymbol U S)) i))) = t := by
    funext i
    exact congrArg t (Fin.ext rfl)
  simpa only [ht]

namespace IsHomomorphism

/-- Original relational homomorphisms are still homomorphisms after
language reindexing, using the same map and not imposing injectivity. -/
theorem asReducedUGraph
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W}
    (h : A.IsHomomorphism B f)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (A.asReducedUGraph U hU).IsHomomorphism
      (B.asReducedUGraph U hU) f := by
  intro S t ht
  exact h (L.fromReducedUGraphSymbol U S)
    (fun i => t (Fin.cast
      (L.reducedUGraphSymbol_arity_from U hU S) i)) ht

end IsHomomorphism
end RelStructure
end StructuralRamsey

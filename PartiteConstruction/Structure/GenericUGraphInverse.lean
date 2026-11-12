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
  by_cases hR : R ∈ U
  · simp [fromReducedUGraph, asReducedUGraph,
      RelLanguage.toReducedUGraphSymbol,
      RelLanguage.fromReducedUGraphSymbol, hR]
    all_goals simp [RelLanguage.toReducedUGraphSymbol,
      RelLanguage.fromReducedUGraphSymbol, hR, Fin.cast]
  · simp [fromReducedUGraph, asReducedUGraph,
      RelLanguage.toReducedUGraphSymbol,
      RelLanguage.fromReducedUGraphSymbol, hR]
    all_goals simp [RelLanguage.toReducedUGraphSymbol,
      RelLanguage.fromReducedUGraphSymbol, hR, Fin.cast]

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
  cases S with
  | inl R =>
      have hR : R.1 ∉ U := R.2
      simp [fromReducedUGraph, asReducedUGraph,
        RelLanguage.toReducedUGraphSymbol,
        RelLanguage.fromReducedUGraphSymbol, hR]
      all_goals simp [RelLanguage.toReducedUGraphSymbol,
        RelLanguage.fromReducedUGraphSymbol, hR, Fin.cast]
  | inr F =>
      have hF : F.1 ∈ U := F.2
      simp [fromReducedUGraph, asReducedUGraph,
        RelLanguage.toReducedUGraphSymbol,
        RelLanguage.fromReducedUGraphSymbol, hF]
      all_goals simp [RelLanguage.toReducedUGraphSymbol,
        RelLanguage.fromReducedUGraphSymbol, hF, Fin.cast]

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

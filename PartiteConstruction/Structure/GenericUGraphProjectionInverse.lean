import PartiteConstruction.Structure.GenericUGraphProjection
import PartiteConstruction.Structure.GenericUGraphPartiteInverse

/-!
# Track F: inverse homomorphism-embedding/partite projection transport

The forward IsPartiteOver bridge preserves the original projection into
the nonredundant U-graph signature. An ARBITRARY graph witness must also
be decoded into a valid original-L partite projection: the reverse
homomorphism-embedding direction cannot be replaced by positive relation
preservation alone.

This module transfers irreducible induced subsets, the actual embedding
witness on every such subset, and the unchanged projection part map.
No cardinality, irreducibility of B, closure or extra coherence premise.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Irreducibility of an original induced subset of a decoded graph
structure implies irreducibility of the corresponding graph subset itself,
using the identical vertices and arity-cast relation tuples. -/
theorem irreducible_graph_induce_of_decoded
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.withUFunctionsReduced U).graph V)
    (S : Set V)
    (hS : ((fromReducedUGraph U hU D).induce S).Irreducible) :
    (D.induce S).Irreducible := by
  intro x y hxy
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
  let F := L.toReducedUGraphSymbol U R
  let hR := L.reducedUGraphSymbol_arity U hU R
  let z' : Fin ((L.withUFunctionsReduced U).graph.arity F) → S :=
    fun k => z (Fin.cast hR k)
  refine ⟨F, z', Fin.cast hR.symm i, Fin.cast hR.symm j,
    ?_, ?_, ?_⟩
  · change D.rel F (Subtype.val ∘ z')
    change D.rel F (fun k => (Subtype.val ∘ z) (Fin.cast hR k)) at hz
    exact hz
  · change z (Fin.cast hR (Fin.cast hR.symm i)) = x
    have hc : Fin.cast hR (Fin.cast hR.symm i) = i := Fin.ext rfl
    simpa only [hc] using hzi
  · change z (Fin.cast hR (Fin.cast hR.symm j)) = y
    have hc : Fin.cast hR (Fin.cast hR.symm j) = j := Fin.ext rfl
    simpa only [hc] using hzj

namespace IsHomomorphismEmbedding

/-- Decode an arbitrary graph-signature homomorphism-embedding into the
original relational language on exactly the same map. Every irreducible
source subset receives the genuine decoded induced embedding. -/
theorem fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure (L.withUFunctionsReduced U).graph V}
    {B : RelStructure (L.withUFunctionsReduced U).graph W}
    {f : V → W}
    (h : A.IsHomomorphismEmbedding B f) :
    (RelStructure.fromReducedUGraph U hU A).IsHomomorphismEmbedding
      (RelStructure.fromReducedUGraph U hU B) f := by
  constructor
  · intro R t ht
    exact h.1 (L.toReducedUGraphSymbol U R)
      (fun k => t (Fin.cast (L.reducedUGraphSymbol_arity U hU R) k)) ht
  · intro S hS
    have hSG : (A.induce S).Irreducible :=
      irreducible_graph_induce_of_decoded U hU A S hS
    obtain ⟨e, he⟩ := h.2 S hSG
    let e' : Embedding
        ((RelStructure.fromReducedUGraph U hU A).induce S)
        (RelStructure.fromReducedUGraph U hU B) :=
      RelStructure.Embedding.fromReducedUGraph U hU e
    refine ⟨e', ?_⟩
    intro x
    change e x = f x.1
    exact he x

end IsHomomorphismEmbedding
end RelStructure

namespace Partite.System

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- The full homomorphism-embedding projection invariant of an ARBITRARY
U-graph partite system survives decoding to original L. -/
theorem isPartiteOver_fromReducedUGraph
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.withUFunctionsReduced U).graph P)
    (B : Partite.System (L.withUFunctionsReduced U).graph P V)
    (hB : B.IsPartiteOver D) :
    (Partite.System.fromReducedUGraph U hU B).IsPartiteOver
      (RelStructure.fromReducedUGraph U hU D) := by
  exact hB.fromReducedUGraph U hU

end Partite.System
end StructuralRamsey

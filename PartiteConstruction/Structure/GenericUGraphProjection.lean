import PartiteConstruction.Structure.GenericUGraphInverse
import PartiteConstruction.Partite.Induced

/-!
# Track F: transport the homomorphism-embedding projection invariant

The original induced partite construction requires its projection to be a
homomorphism-embedding, not merely a positive homomorphism. Arbitrary
relational (L,U)-reindexing preserves irreducible subsets, induced relations,
and restrictions to those subsets, on the same vertex and part maps.

This module builds the forward direction explicitly. The inverse direction
and the full partite-Picture transfer are independent follow-up obligations.
No Ramsey, irreducibility-of-B or closure assumption is added.
-/

namespace StructuralRamsey

universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Original irreducibility implies irreducibility of the exact reindexed
structure. Both require that each pair of distinct vertices occurs in the
same relational tuple, which is unchanged by the symbol/arity equivalence. -/
theorem Irreducible.asReducedUGraph
    {A : RelStructure L V}
    (h : A.Irreducible)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (A.asReducedUGraph U hU).Irreducible := by
  intro x y hxy
  obtain ⟨R, t, i, j, ht, hi, hj⟩ := h hxy
  let S := L.toReducedUGraphSymbol U R
  let hR := L.reducedUGraphSymbol_arity U hU R
  let t' : Fin ((L.withUFunctionsReduced U).graph.arity S) → V :=
    fun k => t (Fin.cast hR k)
  have ht' : (A.asReducedUGraph U hU).rel S t' := by
    have hh := (from_asReducedUGraph_rel_iff A U hU R t).mpr ht
    exact hh
  refine ⟨S, t', Fin.cast hR.symm i, Fin.cast hR.symm j,
    ht', ?_, ?_⟩
  · have hc : Fin.cast hR (Fin.cast hR.symm i) = i :=
      Fin.ext rfl
    change t (Fin.cast hR (Fin.cast hR.symm i)) = x
    simpa only [hc] using hi
  · have hc : Fin.cast hR (Fin.cast hR.symm j) = j :=
      Fin.ext rfl
    change t (Fin.cast hR (Fin.cast hR.symm j)) = y
    simpa only [hc] using hj

/-- Conversely, reindexing cannot create a new pair of vertices sharing
a relation tuple that was not already present in the original L. -/
theorem Irreducible.ofReducedUGraph
    {A : RelStructure L V}
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (h : (A.asReducedUGraph U hU).Irreducible) :
    A.Irreducible := by
  intro x y hxy
  obtain ⟨S, t, i, j, ht, hi, hj⟩ := h hxy
  let R := L.fromReducedUGraphSymbol U S
  let hR := L.reducedUGraphSymbol_arity_from U hU S
  let t' : Fin (L.arity R) → V :=
    fun k => t (Fin.cast hR k)
  have ht' : A.rel R t' :=
    (A.asReducedUGraph_rel_iff U hU S t).mp ht
  refine ⟨R, t', Fin.cast hR.symm i, Fin.cast hR.symm j,
    ht', ?_, ?_⟩
  · have hc : Fin.cast hR (Fin.cast hR.symm i) = i :=
      Fin.ext rfl
    change t (Fin.cast hR (Fin.cast hR.symm i)) = x
    simpa only [hc] using hi
  · have hc : Fin.cast hR (Fin.cast hR.symm j) = j :=
      Fin.ext rfl
    change t (Fin.cast hR (Fin.cast hR.symm j)) = y
    simpa only [hc] using hj

/-- Irreducibility is precisely invariant under arbitrary U-graph
reindexing; no finiteness or arity-two hypothesis is needed. -/
theorem irreducible_asReducedUGraph_iff
    (A : RelStructure L V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (A.asReducedUGraph U hU).Irreducible ↔ A.Irreducible := by
  constructor
  · exact Irreducible.ofReducedUGraph U hU
  · intro h
    exact h.asReducedUGraph U hU

/-- Reindexing commutes literally with restriction to an arbitrary induced
vertex subset, preserving the same subtype carrier and all repeated tuples. -/
theorem induce_asReducedUGraph
    (A : RelStructure L V) (S : Set V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (A.induce S).asReducedUGraph U hU =
      (A.asReducedUGraph U hU).induce S :=
  rfl

namespace IsHomomorphismEmbedding

/-- The original genuine homomorphism-embedding, including inducedness on
every irreducible subset, stays a homomorphism-embedding after arbitrary
relation/function-graph reindexing. The vertex map is identical. -/
theorem asReducedUGraph
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W}
    (h : A.IsHomomorphismEmbedding B f)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (A.asReducedUGraph U hU).IsHomomorphismEmbedding
      (B.asReducedUGraph U hU) f := by
  constructor
  · exact h.1.asReducedUGraph U hU
  · intro S hS
    have hS' : ((A.induce S).asReducedUGraph U hU).Irreducible := by
      simpa only [induce_asReducedUGraph A S U hU] using hS
    have hSorig : (A.induce S).Irreducible :=
      (irreducible_asReducedUGraph_iff (A.induce S) U hU).mp hS'
    obtain ⟨e, he⟩ := h.2 S hSorig
    have e' : Embedding ((A.asReducedUGraph U hU).induce S)
        (B.asReducedUGraph U hU) := by
      rw [← induce_asReducedUGraph A S U hU]
      exact e.asReducedUGraph U hU
    exact ⟨e', he⟩

end IsHomomorphismEmbedding
end RelStructure

namespace Partite.System

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- The actual partite projection continues to be a homomorphism-embedding
after reindexing. This checks the full induced-partite projection invariant,
not just relation preservation. -/
theorem isPartiteOver_asReducedUGraph
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (hB : B.IsPartiteOver A) :
    (B.asReducedUGraph U hU).IsPartiteOver
      (A.asReducedUGraph U hU) := by
  exact hB.asReducedUGraph U hU

end Partite.System
end StructuralRamsey

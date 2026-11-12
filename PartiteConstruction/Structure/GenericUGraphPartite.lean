import PartiteConstruction.Structure.GenericUGraphReindex
import PartiteConstruction.Partite.Basic

/-!
# Partite systems and their embeddings under the exact U-graph reindex

The actual part map is unchanged. Transversality, including its treatment
of repeated tuple entries, transports by the symbol equivalence and the
arity casts. This is not yet an identification with the *function graph*
of a set-valued encoded system; that semantic comparison is a separate
named obligation before the full intermediate partite lemma transfer.
-/

namespace StructuralRamsey.Partite

universe u v w z

variable {L : RelLanguage.{u}}
variable {P : Type v} {V : Type w} {W : Type z}

namespace System

/-- Reindex every relation of an arbitrary L-partite system into the exact
graph signature of the nonredundant U-function language, on the SAME vertex
carrier, part sort and part map. -/
noncomputable def asReducedUGraph
    (B : System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    System (L.withUFunctionsReduced U).graph P V where
  toRelStructure := B.toRelStructure.asReducedUGraph U hU
  part := B.part
  transversal := by
    intro S x hx i j hp
    let R := L.fromReducedUGraphSymbol U S
    let hArity := L.reducedUGraphSymbol_arity_from U hU S
    let t : Fin (L.arity R) → V :=
      fun k => x (Fin.cast hArity k)
    have hB : B.rel R t := hx
    have hi : t (Fin.cast hArity.symm i) = x i := by
      change x (Fin.cast hArity (Fin.cast hArity.symm i)) = x i
      congr 1
      exact Fin.ext rfl
    have hj : t (Fin.cast hArity.symm j) = x j := by
      change x (Fin.cast hArity (Fin.cast hArity.symm j)) = x j
      congr 1
      exact Fin.ext rfl
    have hp' : B.part (t (Fin.cast hArity.symm i)) =
        B.part (t (Fin.cast hArity.symm j)) := by
      simpa only [hi, hj] using hp
    have he := B.transversal R t hB
      (Fin.cast hArity.symm i) (Fin.cast hArity.symm j) hp'
    exact hi.symm.trans (he.trans hj)

@[simp] theorem asReducedUGraph_part
    (B : System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (x : V) :
    (B.asReducedUGraph U hU).part x = B.part x := rfl

/-- The relation reduct of the reindexed partite system is exactly the
reindexed source relation structure. -/
theorem asReducedUGraph_rel_iff
    (B : System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) → V) :
    (B.asReducedUGraph U hU).rel S t ↔
      (B.toRelStructure.asReducedUGraph U hU).rel S t :=
  Iff.rfl

end System

namespace Embedding

variable {A : System L P V} {B : System L P W}

/-- Genuine part-preserving induced embeddings are unchanged as maps by
reindexing all relation symbols. -/
noncomputable def asReducedUGraph
    (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    Embedding (A.asReducedUGraph U hU) (B.asReducedUGraph U hU) where
  toEmbedding := e.toEmbedding.asReducedUGraph U hU
  map_part := e.map_part

@[simp] theorem asReducedUGraph_apply
    (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (x : V) :
    (e.asReducedUGraph U hU) x = e x := rfl

@[simp] theorem asReducedUGraph_comp
    {X : Type*} {C : System L P X}
    (f : Embedding B C) (e : Embedding A B)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (f.comp e).asReducedUGraph U hU =
      (f.asReducedUGraph U hU).comp (e.asReducedUGraph U hU) := by
  apply Embedding.ext
  intro x
  rfl

end Embedding
end StructuralRamsey.Partite

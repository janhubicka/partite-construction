import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Exact published functional sparsening target

The published survey Appendix A theorem `thm:sparseningRamsey` is stated for
set-valued functions, using the FULL homomorphism-embedding notion and STRICT
functional tree amalgams. The present file fixes that exact target without
asserting a proof. Compare the separately verified
`sparseningRamsey_functionalWeakGraph` in `PublishedSparseningScope`.

Keeping both predicates avoids silently using the relational graph variant
to certify a claim about full functions. -/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {U V W P : Type v}

/-- Published property (3), interpreted on genuinely closed full substructures
rather than weak restrictions. -/
def IrreduciblesExtendTo
    (Base : Structure L V) (C : Structure L W) : Prop :=
  ∀ (S : Set W) (hS : C.IsClosed S),
    (C.induce S hS).Irreducible →
    ∃ e : Embedding Base C,
      ∀ z : S, ∃ b : V, z.1 = e b

/-- The three original conclusions, in their genuine function-language
meaning. No weakened graph target or weak global projection is substituted. -/
def PublishedSparseningConclusion
    (A : Structure L U) (Base : Structure L V)
    (D : Structure L P) (κ : Type*) (n : ℕ) : Prop :=
  ∃ (X : Type v) (_ : Finite X) (C : Structure L X),
    Arrow A Base C κ ∧
    ∃ p : X → P,
      C.IsHomomorphismEmbedding D p ∧
      LocallyClosedTreeCompletable Base C n ∧
      IrreduciblesExtendTo Base C

end StructuralRamsey.Structure

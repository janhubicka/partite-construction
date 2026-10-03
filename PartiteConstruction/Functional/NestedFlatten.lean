import PartiteConstruction.Functional.ClosedPictureRepair
import PartiteConstruction.Partite.Induced

/-! # Flattening nested partite systems

The recursive construction temporarily builds a system partite over an
intermediate picture O, while O is itself partite over the original base D.
This file verifies the flattening back to D.

The relational projection invariant composes automatically.  For
U-transversality, it is enough that every tuple of the inner system is covered
by a closed copy of the previous outer-partite stage whose map respects the
outer D-parts.
-/
namespace StructuralRamsey.Partite.Nested

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P W V X : Type v}

/-- Flatten a C-system over the vertex set of O to the outer part set P. -/
def flatten
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure) :
    Partite.System L.graph P X where
  toRelStructure := C.toRelStructure
  part x := O.part (C.part x)
  transversal R t ht i j hp := by
    have hO :
        O.rel R (C.part ∘ t) :=
      hC.1 R t ht
    have hinner :
        C.part (t i) = C.part (t j) := by
      apply O.transversal R (C.part ∘ t) hO i j
      exact hp
    exact C.transversal R t ht i j hinner

@[simp] theorem flatten_part
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure)
    (x : X) :
    (flatten O C hC).part x = O.part (C.part x) :=
  rfl

/-- Nested homomorphism-embedding projections compose after flattening. -/
theorem flatten_isPartiteOver
    {D : RelStructure L.graph P}
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hO : O.IsPartiteOver D)
    (hC : C.IsPartiteOver O.toRelStructure) :
    (flatten O C hC).IsPartiteOver D := by
  change
    C.toRelStructure.IsHomomorphismEmbedding D
      (O.part ∘ C.part)
  exact hO.comp hC

/-- A closed copy of an outer P-partite system inside the inner carrier,
together with preservation of the outer parts. -/
structure OuterClosedEmbedding
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X) where
  toRelClosed :
    RelStructure.ClosedEmbedding B.toRelStructure C.toRelStructure
  map_outer_part :
    ∀ b, O.part (C.part (toRelClosed b)) = B.part b

instance
    {B : Partite.System L.graph P V}
    {O : Partite.System L.graph P W}
    {C : Partite.System L.graph W X} :
    CoeFun (OuterClosedEmbedding B O C) (fun _ => V → X) :=
  ⟨fun e => e.toRelClosed⟩

/-- An outer-part-preserving closed copy becomes a closed partite embedding
after flattening. -/
def OuterClosedEmbedding.toFlatten
    {B : Partite.System L.graph P V}
    {O : Partite.System L.graph P W}
    {C : Partite.System L.graph W X}
    (hC : C.IsPartiteOver O.toRelStructure)
    (e : OuterClosedEmbedding B O C) :
    Partite.Closed.Embedding B (flatten O C hC) := by
  let pe : Partite.Embedding B (flatten O C hC) := {
    toEmbedding := e.toRelClosed.toEmbedding
    map_part := e.map_outer_part
  }
  exact ⟨pe, e.toRelClosed.closed⟩

/-- Every tuple of C is covered by an outer-part-preserving closed B-copy. -/
def OuterTupleCovered
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X) : Prop :=
  ∀ (R : L.graph.Symbol) (t : Fin (L.graph.arity R) → X),
    C.rel R t →
      ∃ e : OuterClosedEmbedding B O C,
        ∃ q : Fin (L.graph.arity R) → V,
          B.rel R q ∧ t = e ∘ q

/-- Outer tuple coverage turns into the ordinary closed-copy coverage of the
flattened system. -/
theorem flatten_tupleCovered
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure)
    (hCover : OuterTupleCovered B O C) :
    ClosedRepair.TupleCoveredByClosedCopies
      B (flatten O C hC)
      (fun e : OuterClosedEmbedding B O C => e.toFlatten hC) := by
  intro R t ht
  obtain ⟨e, q, hq, heq⟩ := hCover R t ht
  exact ⟨e, q, hq, heq⟩

/-- The precise recursive-construction transversality inference:
if every inner tuple is covered by an outer-part-preserving closed copy of the
previous U-transversal stage, then flattening back to D is U-transversal. -/
theorem flatten_uTransversal
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure)
    (hB : B.FunctionOutputTransversal)
    (hCover : OuterTupleCovered B O C) :
    (flatten O C hC).FunctionOutputTransversal := by
  exact ClosedRepair.uTransversal_of_tupleCovered
    B (flatten O C hC)
    (fun e : OuterClosedEmbedding B O C => e.toFlatten hC)
    hB (flatten_tupleCovered B O C hC hCover)

end StructuralRamsey.Partite.Nested

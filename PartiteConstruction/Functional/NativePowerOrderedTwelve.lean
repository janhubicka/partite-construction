import PartiteConstruction.Functional.NativePowerOrderedPower

/-! # The exact closed twelve-vertex test in the ordered native power

The ordered base has a hereditarily irreducible graph and the ordered
seven-vertex stage is a genuine strict full-functional B-tree with an
EHN weak projection. The added pairwise relation changes neither the
vertex parts nor any function fibre in the native coordinatewise power.

The bijective full functional reduct map from the unexpanded power
therefore transports the *existing closed twelve-vertex staircase*
without adding a function-closure hull. A strict total-fibre completion
in the ordered language would give a forbidden full homomorphism of
that same closed test into the functional reduct of an ordered B-tree.

This is an obstruction to the 2026 survey's total-fibre completion
maps; under the original 2019 partial-function homomorphism convention
the same native staircase *does* have a one-copy completion.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The precise image of the original twelve-vertex support under the
bijective reduct map between *genuine tagged* powers. -/
def OrderedStaircaseSupport : Set OrderedPowerVertex :=
  Set.range (fun x : StaircaseSupport => orderedVertexEquiv x.1)

/-- Full function embeddings have closed ranges. No further vertices
are adjoined, and closure is identical in the ordered language/reduct. -/
theorem orderedStaircaseSupport_closed :
    actualOrderedPower.IsClosed OrderedStaircaseSupport := by
  let inc : Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      actualPower :=
    inclusion actualPower StaircaseSupport staircaseSupport_closed
  let e : Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      actualOrderedPower.linearOrderReduct :=
    oldPower_into_orderedReduct.comp inc
  have hClosed : actualOrderedPower.linearOrderReduct.IsClosed (Set.range e) :=
    e.isHomomorphism.range_isClosed
  change actualOrderedPower.IsClosed OrderedStaircaseSupport at hClosed
  exact hClosed

/-- Each old supported vertex determines exactly one ordered supported
vertex. The map does not depend on a choice of closure generators. -/
def staircaseToOrdered (x : StaircaseSupport) :
    OrderedStaircaseSupport :=
  ⟨orderedVertexEquiv x.1, ⟨x,rfl⟩⟩

theorem staircaseToOrdered_injective :
    Function.Injective staircaseToOrdered := by
  intro x y h
  apply Subtype.ext
  exact orderedVertexEquiv.injective (congrArg Subtype.val h)

theorem staircaseToOrdered_surjective :
    Function.Surjective staircaseToOrdered := by
  intro y
  obtain ⟨x,hx⟩ := y.2
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

noncomputable def staircaseOrderedEquiv :
    StaircaseSupport ≃ OrderedStaircaseSupport :=
  Equiv.ofBijective staircaseToOrdered
    ⟨staircaseToOrdered_injective, staircaseToOrdered_surjective⟩

/-- Exact cardinality is preserved by the vertex bijection: even with
the extra order symbol this is a *proper* closed twelve-vertex test. -/
theorem orderedStaircaseSupport_card_eq_twelve :
    Nat.card OrderedStaircaseSupport = 12 := by
  have h1 : Nat.card StaircaseSupport ≤ Nat.card OrderedStaircaseSupport :=
    Nat.card_le_card_of_injective
      staircaseToOrdered staircaseToOrdered_injective
  have h2 : Nat.card OrderedStaircaseSupport ≤ Nat.card StaircaseSupport :=
    Nat.card_le_card_of_injective
      staircaseOrderedEquiv.symm staircaseOrderedEquiv.symm.injective
  rw [staircaseSupport_card_eq_twelve] at h1 h2
  omega

/-- The full functional reduct embedding of the closed test factors
through the closed induced *ordered* test. -/
noncomputable def staircaseIntoOrderedInduced :
    Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      (actualOrderedPower.induce OrderedStaircaseSupport
        orderedStaircaseSupport_closed).linearOrderReduct := by
  let incOld : Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      actualPower :=
    inclusion actualPower StaircaseSupport staircaseSupport_closed
  let intoPower : Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      actualOrderedPower.linearOrderReduct :=
    oldPower_into_orderedReduct.comp incOld
  let incOrdered : Embedding
      (actualOrderedPower.induce OrderedStaircaseSupport
        orderedStaircaseSupport_closed)
      actualOrderedPower :=
    inclusion actualOrderedPower OrderedStaircaseSupport
      orderedStaircaseSupport_closed
  let incRed : Embedding
      (actualOrderedPower.induce OrderedStaircaseSupport
        orderedStaircaseSupport_closed).linearOrderReduct
      actualOrderedPower.linearOrderReduct :=
    incOrdered.linearOrderReduct
  have hRange : ∀ x : StaircaseSupport,
      ∃ y : OrderedStaircaseSupport, intoPower x = incRed y := by
    intro x
    exact ⟨staircaseToOrdered x,rfl⟩
  exact intoPower.factorThroughClosedRange incRed hRange

/-- No strict total-fibre completion of the proper twelve-vertex closed
test is possible in the ordered language, even though the base graph is
hereditarily irreducible and the input stage is itself a strict tree. -/
theorem orderedStaircaseSupport_no_strictTreeCompletion :
    ¬ HasTreeCompletion toyBaseOrdered
      (actualOrderedPower.induce OrderedStaircaseSupport
        orderedStaircaseSupport_closed) := by
  rintro ⟨W,T,hTree,f,hf⟩
  have hTreeRed : TreeAmalgam toyBase W T.linearOrderReduct := by
    simpa only [toyBaseOrdered_reduct] using
      hTree.linearOrderReduct toyBase_irreducible
  have hfRed :
      (actualOrderedPower.induce OrderedStaircaseSupport
        orderedStaircaseSupport_closed).linearOrderReduct.IsHomomorphism
          T.linearOrderReduct f := by
    constructor
    · intro R x hx
      exact hf.1.1 (.inl R) x hx
    · exact hf.1.2
  let e := staircaseIntoOrderedInduced
  have hfOld :
      (actualPower.induce StaircaseSupport
        staircaseSupport_closed).IsHomomorphism T.linearOrderReduct
          (f ∘ e) :=
    hfRed.comp e.isHomomorphism
  exact staircaseSupport_no_fullTreeHom hTreeRed (f ∘ e) hfOld

end StructuralRamsey.Structure.NativePowerObstruction

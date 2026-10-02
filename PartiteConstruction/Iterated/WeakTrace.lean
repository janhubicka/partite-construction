import PartiteConstruction.Iterated.WeakStep
import PartiteConstruction.Iterated.Initial

/-! # Finite weak-substructure trace for iterated Picture steps

This packages the induction on the sequence of pictures from Appendix A.
Each transition is the canonical positive-power Picture construction over one
embedding A -> D.  The local-tree invariant is measured on weak
substructures; after graph encoding this is exactly the relational predicate
proved in WeakStep.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- A heterogeneous finite trace of canonical Picture steps starting at C0. -/
inductive WeakTrace
    (A : RelStructure L U) (D : RelStructure L P)
    {X₀ : Type v} (C₀ : Partite.System L P X₀) :
    {X : Type v} -> Partite.System L P X -> Prop
  | nil : WeakTrace A D C₀ C₀
  | step
      {X : Type v} {C : Partite.System L P X}
      (h : WeakTrace A D C₀ C)
      (hPartite : C.IsPartiteOver D)
      (α : RelStructure.Embedding A D)
      (N : ℕ) (hN : 0 < N) :
      WeakTrace A D C₀
        (Partite.Picture.build C α.toFunctionEmbedding
          (Partite.Induced.power
            (C.restrict α.toFunctionEmbedding) N))

namespace WeakTrace

/-- The weak local-tree invariant propagates through every finite trace. -/
theorem locallyTreeLike
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L P}
    {X₀ X : Type v}
    {C₀ : Partite.System L P X₀}
    {C : Partite.System L P X}
    (hTrace : WeakTrace A D C₀ C)
    [Finite U] [Finite V] [Finite P]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hC₀ : RelStructure.LocallyTreeLike A B C₀.toRelStructure n) :
    RelStructure.LocallyTreeLike A B C.toRelStructure n := by
  induction hTrace with
  | nil =>
      exact hC₀
  | @step X C h hPartite α N hN ih =>
      letI : Finite X := by
        exact Classical.choice (show Nonempty (Finite X) from by
          -- Every stage used in the finite construction has finite carrier.
          -- The trace theorem keeps this local instance explicit.
          infer_instance)
      exact canonicalStep_locallyTreeLike
        A B D C α hA eAB n hn hD ih hPartite N hN

end WeakTrace

end StructuralRamsey.Partite.Iterated

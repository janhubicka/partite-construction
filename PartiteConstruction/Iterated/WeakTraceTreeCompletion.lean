import PartiteConstruction.Iterated.WeakStepTreeCompletion
import PartiteConstruction.Iterated.WeakTrace

/-! # Finite Picture traces for local tree completability

The fixed base D carries the stronger projected-history coherence only at the
lower level n-1.  Along the actual finite Picture trace, the moving stage
needs only local tree completability at level n.  The one-step theorem
therefore iterates directly through the whole trace.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- Local tree completability propagates through every canonical Picture
trace, under projected-history coherence of the fixed base. -/
theorem WeakTrace.locallyTreeCompletable
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L P}
    {X₀ X : Type v}
    {C₀ : Partite.System L P X₀}
    {C : Partite.System L P X}
    (hTrace : WeakTrace A D C₀ C)
    [Finite U] [Finite V] [Finite P]
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD :
      RelStructure.ProjectedHistoryLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id (n - 1))
    (hC₀ :
      RelStructure.LocallyTreeCompletable B C₀.toRelStructure n) :
    RelStructure.LocallyTreeCompletable B C.toRelStructure n := by
  induction hTrace with
  | nil =>
      exact hC₀
  | @step X C finiteC h hPartite α N hN ih =>
      letI : Finite X := finiteC
      exact canonicalStep_locallyTreeCompletable_projectedHistory
        A B D C α hA eAB n hn hD ih hPartite N hN

end StructuralRamsey.Partite.Iterated

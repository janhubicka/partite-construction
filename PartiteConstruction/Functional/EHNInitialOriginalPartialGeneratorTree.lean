import PartiteConstruction.Functional.OriginalPartialSmallImageGeneratorHull
import PartiteConstruction.Functional.InitialTreeCompletion
import PartiteConstruction.Functional.EHNPowerOriginalPartialTree

/-!
# Published initial Picture for strict original-partial generator-rank tests

The original functional EHN initial Picture is a genuine strict
full-functional B-tree when B is irreducible and all function
symbols have positive arity. The generator-rank strict local
invariant is therefore true at EVERY rank for the actual
initial stage. This reuses the already verified functional
initial construction rather than replacing it with a U-closed
relational structure or repeating the Ramsey recursion.

The unresolved step for a strict functional n-pass theorem is
preservation through mixed Picture attachments over reducible roots,
with compatible rooted side completions.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- Actual native positive-arity initial Picture carries the strict
full-functional original-partial generator-rank invariant at ANY k
and still represents every full B-placement in D. -/
theorem initial_originalPartial_generatorRank
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V] [Finite P]
    (hBase : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (beta0 : Structure.Embedding Base D)
    (k : ℕ) :
    ∃ T : Stage K D,
      Structure.LocallyGeneratedOriginalPartialTreeCompletable
        Base T.system.toStructure k ∧
      ∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  obtain ⟨T, hTree, hCopies⟩ :=
    initial_tree hK Base hBase hBIrr hPos beta0
  classical
  exact ⟨T,
    Structure.LocallyGeneratedOriginalPartialTreeCompletable.of_tree
      hTree k,
    hCopies⟩


/-- The ENTIRE genuine native Hales--Jewett core has a strict one-copy
original-partial B-tree completion. Consequently every function-closed
test in that core, at any generator rank, has a strict partial
completion by restricting the same EHN projection. No weak test
or artificially enlarged closure hull is used. -/
theorem power_originalPartial_generatorRank
    {VB : Type v}
    (A : Structure L P)
    (R : System L P V)
    (hR : R.WeaklyPartiteOver A)
    (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (N : ℕ) (hN : 0 < N) (k : ℕ) :
    Structure.LocallyGeneratedOriginalPartialTreeCompletable
      Base (Induced.power R N).toStructure k := by
  have hCore : Structure.HasOriginalPartialTreeCompletion
      Base (Induced.power R N).toStructure :=
    FunctionalPartite.Induced.power_hasOriginalPartialTreeCompletion
      A R hR Base eAB N hN
  intro H hH _
  let e : Structure.Embedding
      ((Induced.power R N).toStructure.induce H hH)
      (Induced.power R N).toStructure :=
    Structure.inclusion (Induced.power R N).toStructure H hH
  exact hCore.pullback e.isEHNHomomorphismEmbedding.toOriginalPartial

end StructuralRamsey.FunctionalPartite.EHN

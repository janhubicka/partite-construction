import PartiteConstruction.Functional.OriginalPartialSmallImageGeneratorHull
import PartiteConstruction.Functional.InitialTreeCompletion

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
  exact ⟨T,
    Structure.LocallyGeneratedOriginalPartialTreeCompletable.of_tree
      hTree k,
    hCopies⟩

end StructuralRamsey.FunctionalPartite.EHN

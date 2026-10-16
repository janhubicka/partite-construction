import PartiteConstruction.Functional.AmbientRelativeOneCopyCore
import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.WeakInvariant

/-!
# The ACTUAL native Hales–Jewett functional core is output-transversal

A partite function image must have at most ONE output in each part.
This is a field of every `FunctionalPartite.System`, and is
preserved by the genuine coordinatewise functional Hales–Jewett
power, not inferred from singleton-valuedness.

Specialize the general one-copy ambient-relative weak tree witness to
the *actual* Hales–Jewett power of a weakly partite system. Every
individual function value in the power maps injectively to its part
set, while every weak test of the power has an ambient-relative
functional completion in one full Base-copy via its EHN projection.

The resulting target is a STRICT FUNCTIONAL one-copy Base tree, not
a relational graph tree. The support and mixed attachments require
the additional gluing lemmas; the theorem does not postulate them.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W : Type v}

/-- In the genuine set-valued Hales–Jewett power, output fibres
remain transversal, and every weak test has a strict one-copy
B-tree ambient-relative witness when the selected source A embeds
fully into B. No singleton-valuedness is assumed. -/
theorem power_oneCopyTree_transversal
    (A : Structure L P) (B : System L P V)
    (hB : B.WeaklyPartiteOver A)
    (N : ℕ) (hN : 0 < N)
    (Base : Structure L W)
    (eAB : Structure.Embedding A Base) :
    (∀ F (x : Fin (L.funcArity F) → Vertex B N),
      Set.InjOn (power B N).part ((power B N).func F x)) ∧
    ∀ S : Set (Vertex B N),
      ∃ f : S → W,
        IsAmbientRelativeWeakHE
          (power B N).toStructure S Base f ∧
        TreeAmalgam Base W Base := by
  constructor
  · intro F x
    exact (power B N).func_part_injOn F x
  · intro S
    have hPower : (power B N).WeaklyPartiteOver A :=
      power_weaklyPartiteOver hB hN
    exact hPower.ambientRelativeWeak_oneCopyTree eAB S

end StructuralRamsey.FunctionalPartite.Induced

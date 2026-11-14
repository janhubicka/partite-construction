import PartiteConstruction.Structure.GenericUOutputTransversal
import PartiteConstruction.Partite.Induced
import PartiteConstruction.Structure.GenericUFunctionalDictionary

/-!
# Track F — U-output transversality of the actual original induced power

The function-graph proof of the induced partite lemma preserves output-fibre
uniqueness in each named part. This module proves that assertion *directly*
for an arbitrary original relational (L,U), and for the actual coordinatewise
power B^N from Partite.Induced, not an abstract isomorphic replacement.

No Hales–Jewett length positivity, Ramsey hypothesis, irreducibility,
or finite language restriction is required for this structural fact.
-/

namespace StructuralRamsey.Partite.System
universe u v

variable {L : RelLanguage.{u}} {P V : Type v}

/-- If every original distinguished relation R has at most one last output
in each part for a fixed root tuple, then the ACTUAL induced coordinate
power B^N has that same U-output transversality. This includes N=0,
repeated tuple entries, and all empty/multivalued relation fibres. -/
theorem originalUOutputTransversal_power
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (hB : B.OriginalUOutputTransversal U hU)
    (N : ℕ) :
    (Partite.Induced.power B N).OriginalUOutputTransversal U hU := by
  intro F x y z hy hz hp
  apply Partite.NonInduced.Vertex.ext B hp
  intro k
  let g : Partite.NonInduced.Vertex B N → V := fun q => q.coord k
  let args : Fin (L.arity F.1 - 1) → V := g ∘ x
  have hcompY :=
    RelLanguage.appendU_comp L U hU F g x y
  have hcompZ :=
    RelLanguage.appendU_comp L U hU F g x z
  have hyk : B.rel F.1
      (RelLanguage.appendU L U hU F args (y.coord k)) := by
    have hh : B.rel F.1
        (g ∘ RelLanguage.appendU L U hU F x y) := hy k
    exact Eq.mp (congrArg (B.rel F.1) hcompY) hh
  have hzk : B.rel F.1
      (RelLanguage.appendU L U hU F args (z.coord k)) := by
    have hh : B.rel F.1
        (g ∘ RelLanguage.appendU L U hU F x z) := hz k
    exact Eq.mp (congrArg (B.rel F.1) hcompZ) hh
  have hparts : B.part (y.coord k) = B.part (z.coord k) :=
    (y.belongs k).trans (hp.trans (z.belongs k).symm)
  exact hB F args (y.coord k) (z.coord k) hyk hzk hparts

end StructuralRamsey.Partite.System

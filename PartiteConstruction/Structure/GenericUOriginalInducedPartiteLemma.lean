import PartiteConstruction.Structure.GenericUClosedPartiteArrow
import PartiteConstruction.Structure.GenericUGraphPowerClosedEmbedding
import PartiteConstruction.Structure.GenericUPowerOutputTransversal

/-!
# Track F — literal induced partite lemma with U-closures for arbitrary (L,U)

This formalizes the exact printed intermediate lemma lem:indpartiteU
from the classification-programme survey in the original relational L,
with U a family of distinguished relations of arity at least two.

The proof transfers the verified Hales--Jewett function-graph lemma on
the same vertices and part maps. Its target is the ACTUAL power B^N,
not an abstract Ramsey witness. No statement is considered verified
until full exact-head Lean compilation and axiom audit pass.
-/

namespace StructuralRamsey.Partite
universe u v

namespace System

/-- The transversal partite expansion commutes with the same-carrier
generic U-graph reindexing. -/
@[simp] theorem transversal_asReducedUGraph
    {L : RelLanguage.{u}} {P : Type v}
    (A : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    (Partite.transversal A).asReducedUGraph U hU =
      Partite.transversal (A.asReducedUGraph U hU) := by
  rfl

end System

namespace OriginalUClosed

/-- The exact arbitrary-relational induced partite lemma with closures.
The target is the genuine coordinate power B^N; no irreducibility,
B-closedness, extra coherence or finite-language premise is imposed. -/
theorem inducedPartiteLemma
    {L : RelLanguage.{u}} {P V : Type v}
    (A : RelStructure L P)
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    (hPart : B.IsPartiteOver A)
    (hT : B.OriginalUOutputTransversal U
      (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)))
    [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ (N : ℕ), 0 < N ∧
      (Partite.Induced.power B N).OriginalUOutputTransversal U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) ∧
      Arrow (Partite.transversal A) B
        (Partite.Induced.power B N) U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR))
        κ := by
  classical
  let hU1 : ∀ R, R ∈ U → 1 ≤ L.arity R :=
    fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)
  let AG := A.asReducedUGraph U hU1
  let BG := B.asReducedUGraph U hU1
  have hPartG : BG.IsPartiteOver AG :=
    Partite.System.isPartiteOver_asReducedUGraph A B U hU1 hPart
  have hTG : BG.FunctionOutputTransversal :=
    (B.originalUOutputTransversal_iff U hU1).mp hT
  obtain ⟨N, hN, _hPowerTG, hArrowG⟩ :=
    Partite.Closed.Induced.partiteLemma
      (A := AG) (B := BG) hPartG hTG κ
  have hArrowPower : Partite.Closed.Arrow
      (Partite.transversal AG) BG
      ((Partite.Induced.power B N).asReducedUGraph U hU1) κ :=
    Partite.Closed.arrow_of_closed_target
      (Partite.closedFromGraphPower B U hU1 N) κ hArrowG
  have hOriginal : Arrow
      (Partite.transversal A) B (Partite.Induced.power B N)
      U hU1 κ := by
    exact (arrow_iff_graph
      (Partite.transversal A) B (Partite.Induced.power B N)
      U hU1 κ).mpr (by
        simpa only [Partite.System.transversal_asReducedUGraph]
          using hArrowPower)
  exact ⟨N, hN,
    Partite.System.originalUOutputTransversal_power B U hU1 hT N,
    hOriginal⟩

end OriginalUClosed
end StructuralRamsey.Partite

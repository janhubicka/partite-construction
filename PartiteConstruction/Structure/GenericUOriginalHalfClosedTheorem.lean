import PartiteConstruction.Structure.GenericUOriginalHalfClosedArrow
import PartiteConstruction.Structure.GenericUOriginalClosedArrowGraphWitness
import PartiteConstruction.Structure.GenericUGraphProjectionInverse
import PartiteConstruction.Structure.GenericUWitnessTransversality
import PartiteConstruction.Structure.GenericUReducedLanguage
import PartiteConstruction.Functional.HalfClosedTheorem

/-!
# Track F — literal arbitrary-relational half-U-closed partite witness

The input is the original survey half-closed arrow with an ordinary B→D
copy whose composites with all U-closed A→B copies have closed lifts.
The nonredundant graph language encodes this without changing maps.
The established graph half-closed partite construction supplies a
genuine graph D-partite, output-transversal Ramsey witness.
The inverse U-reindex yields the original-L witness on identical vertices,
with original projection, fibre transversality and full closed Ramsey arrow.

No coherence, irreducibility, full-fibre-surjective projection or
finite-language hypothesis is inserted.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P T V : Type v}

/-- The original relation structure is literally equal to its decoded
reduced U-function graph, on the same carrier and every relation. -/
theorem originalU_graphRoundtrip_eq
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    fromReducedUGraph U hU (D.asReducedUGraph U hU) = D := by
  apply RelStructure.mk.injEq.mpr
  funext R t
  exact propext (D.from_asReducedUGraph_rel_iff U hU R t)

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Partite.OriginalUClosed

universe u v
variable {L : RelLanguage.{u}} {P T V : Type v}

/-- The actual half-U-closed induced partite construction for arbitrary
original relational L and U symbols of arity >= 2. No output extra
hypotheses: the existential witness is D-partite, U-transversal and
satisfies the full original U-closed induced Ramsey arrow. -/
theorem halfClosedPartiteWitness
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    [Finite T] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.OriginalUHalfClosedArrow A B D U
      (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) κ) :
    ∃ (X : Type v) (_ : Finite X) (C : Partite.System L P X),
      C.IsPartiteOver D ∧
      C.OriginalUOutputTransversal U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) ∧
      RelStructure.OriginalUClosedArrow A B C.toRelStructure U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR))
        κ := by
  classical
  let hU1 : ∀ R, R ∈ U → 1 ≤ L.arity R :=
    fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)
  let A_g := A.asReducedUGraph U hU1
  let B_g := B.asReducedUGraph U hU1
  let D_g := D.asReducedUGraph U hU1
  have hpos : (L.withUFunctionsReduced U).PositiveFuncArity :=
    L.withUFunctionsReduced_positive U hU
  have hG : RelStructure.HalfClosedArrow A_g B_g D_g κ :=
    (RelStructure.originalUHalfClosedArrow_iff_graph A B D U hU1 κ).mp hRamsey
  obtain ⟨X, hX, C_g, hCPartG, hCTG, hArrowG⟩ :=
    Partite.HalfClosed.ramseyPartiteWitness A_g B_g D_g hpos κ hG
  let C := Partite.System.fromReducedUGraph U hU1 C_g
  have hPart : C.IsPartiteOver D := by
    have hPartDecoded :
        C.IsPartiteOver (RelStructure.fromReducedUGraph U hU1 D_g) :=
      Partite.System.isPartiteOver_fromReducedUGraph
        U hU1 D_g C_g hCPartG
    rw [RelStructure.originalU_graphRoundtrip_eq D U hU1] at hPartDecoded
    exact hPartDecoded
  have hTrans : C.OriginalUOutputTransversal U hU1 :=
    (Partite.System.originalUOutputTransversal_decode_iff
      U hU1 C_g).mpr hCTG
  have hArrow : RelStructure.OriginalUClosedArrow
      A B C.toRelStructure U hU1 κ :=
    RelStructure.originalUClosedArrow_of_graphWitness
      A B U hU1 C_g κ hArrowG
  exact ⟨X, hX, C, hPart, hTrans, hArrow⟩

end StructuralRamsey.Partite.OriginalUClosed

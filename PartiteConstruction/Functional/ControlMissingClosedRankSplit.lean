import PartiteConstruction.Functional.ControlMissingOutputDichotomy
import PartiteConstruction.Functional.EHNDomainFailureDecompose

/-!
# Exact cardinal rank decrease from a control phantom on a CLOSED weak test

The control/source missing-output dichotomy says that, on a genuinely
function-closed exact weak source test, an output requested by the
control but absent from the source must be a DOMAIN-REFLECTION FAILURE.

The existing verified EHN closed-test decomposition theorem then
splits the WHOLE ORIGINAL finite test by a proper full functional
free amalgam, whose two sides and common root each have strictly
fewer vertices than the original test. This is stronger than
merely finding a proper decomposition of the input-generated hull.

The conclusion applies ONLY to closed finite source tests. It
does not replace the nonclosed weak-test history/root-profile
compatibility missing from the strict functional Appendix A n-pass.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- On a function-closed FINITE test of a real EHN partite system,
a control-required output absent from the exact source weak test
gives a PROPER free decomposition of the entire original induced
test, with strict vertex-cardinality drops on both sides and root.

All carriers are the actual test vertices, never a closure-hull
substitute for the tested S. -/
theorem System.controlMissing_closedFiniteTest_decompose
    (B : System L P V) (D : Structure L P)
    [Finite V]
    (hB : B.WeaklyPartiteOver D)
    (S : Finset V)
    (hClosed : B.toStructure.IsClosed (↑S : Set V))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → ↥(↑S : Set V))
    (q : P)
    (hControl : B.ControlMissingAtPart D (↑S : Set V) F xs q) :
    let Small := B.toStructure.induce (↑S : Set V) hClosed
    ∃ d : ProperFreeDecomposition Small,
      Nat.card d.Left < Nat.card ↥(↑S : Set V) ∧
      Nat.card d.Right < Nat.card ↥(↑S : Set V) ∧
      Nat.card d.Common < Nat.card ↥(↑S : Set V) := by
  have hPhantom : B.ProjectedUndefinedAtPart
      D (↑S : Set V) F xs q :=
    (B.controlMissing_of_closed_iff_projectedUndefined
      D hB (↑S : Set V) hClosed F xs q).mp hControl
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part :=
    hB
  have hTarget :
      (D.func F ((B.part ∘ Subtype.val) ∘ xs)).Nonempty := by
    refine ⟨q, ?_⟩
    simpa only [Function.comp_assoc] using hPhantom.2
  have hSource :
      ¬ ((B.toStructure.induce (↑S : Set V) hClosed).func F xs).Nonempty := by
    change ¬ (B.func F (Subtype.val ∘ xs)).Nonempty
    exact hPhantom.1
  exact hp.closedTest_decompose_of_domainFailure
    S hClosed F xs hTarget hSource

end StructuralRamsey.FunctionalPartite

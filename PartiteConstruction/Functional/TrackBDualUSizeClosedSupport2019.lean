import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019
import PartiteConstruction.Functional.NativePartialClosure
import PartiteConstruction.Functional.NativeWholePartClosure
import PartiteConstruction.Functional.EHNStage

/-!
# Track B: exact qualified comparison of the two 2019 U-size presentations

The native functional survey's clipped weak restriction and the genuine
2019 Option(Set) whole-fibre weak restriction agree on a given exact S
if and only if no original function fibre is partly retained by S.

Under exactly this condition, the *different* canonical 2019 tagged
source presentations have the same minimum-generator USize at every n:
the split-output patternGraph presentation, and the ambient complete
whole-mask presentation. The proof is an equality of the actual weak
function structures, not a false isomorphism of these tagged languages.

Every genuinely function-closed source subset satisfies this condition.
In particular, the selected closed A-support in an actual EHN Stage
admits both rank presentations on its exact carrier, without replacing
the support by a function-generated hull.

No general equivalence is claimed for arbitrary weak cuts; the
transversal multivalued crossing regression refutes that shortcut.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]

/-- Both canonical ambient 2019 USize presentations have identical
bounds on the SAME weak S, provided no native function fibre is partly
retained on S. One tag is output-part-split and clipped; the other has
complete ambient OLD masks and whole-fibre Option(Set) semantics.

This proves equivalence of the *rank predicates*, not of the complete
tagged structures or their relational powers. -/
theorem System.clippedUSize_iff_wholeMaskUSize_of_noPartial
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) [Fintype S] (n : ℕ)
    (hNo : NoPartiallyRetainedValues B.toStructure.toNonemptyPartial S) :
    (USize (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) ≤ n) ↔
    (USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) ≤ n) := by
  have hClipped :=
    B.weakGeneratedByAtMost_iff_outputTaggedUSize_le hPos S n
  have hWhole :=
    B.toStructure.toNonemptyPartial.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      B.part hPos B.toNonemptyPartial_fibreTransversal S n
  have hEqual :
      (B.toStructure.weakInduce S).toNonemptyPartial =
        wholeWeakInduce B.toStructure.toNonemptyPartial S :=
    (Structure.toNonemptyPartial_weakInduce_eq_whole_iff
      B.toStructure S).mpr hNo
  have hFaithful :=
    (B.toStructure.weakInduce S).toNonemptyPartial_generatedByAtMost_iff n
  calc
    _ ↔ (B.toStructure.weakInduce S).GeneratedByAtMost n := hClipped.symm
    _ ↔ ((B.toStructure.weakInduce S).toNonemptyPartial).GeneratedByAtMost n :=
      hFaithful.symm
    _ ↔ (wholeWeakInduce B.toStructure.toNonemptyPartial S).GeneratedByAtMost n := by
      rw [hEqual]
    _ ↔ _ := hWhole

/-- A function-closed ambient cut has no partially retained output
fibre, so the exact clipped and whole-fibre USize thresholds agree,
including multivalued transversal fibres and all finite weak ranks. -/
theorem System.clippedUSize_iff_wholeMaskUSize_of_closed
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    [Fintype S] (n : ℕ) :
    (USize (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) ≤ n) ↔
    (USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) ≤ n) := by
  have hPS : B.toStructure.toNonemptyPartial.IsClosed S :=
    (Structure.toNonemptyPartial_isClosed_iff B.toStructure S).mpr hS
  have hNo : NoPartiallyRetainedValues
      B.toStructure.toNonemptyPartial S := by
    intro F xs U hU
    left
    exact hPS F (Subtype.val ∘ xs) U (fun i => (xs i).2) hU
  exact B.clippedUSize_iff_wholeMaskUSize_of_noPartial hPos S n hNo

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P U : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual selected A-support of every genuine EHN Stage is
function-closed, hence its clipped and whole-fibre ambient 2019
USize thresholds agree on the SAME native vertices.

The support is the REAL support used in the Picture free attachments,
not an enlarged hull or a synthesized OLD relational test. -/
theorem Stage.selectedSupport_clippedUSize_iff_wholeMaskUSize
    (T : Stage K D)
    (A : Structure L U) (α : Structure.Embedding A D)
    (hPos : L.PositiveFuncArity) (n : ℕ) :
    let S := T.system.support α.toFunctionEmbedding
    (USize (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce S) ≤ n) ↔
    (USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph T.system.part)).induce S) ≤ n) := by
  classical
  let S := T.system.support α.toFunctionEmbedding
  letI : Fintype S := Fintype.ofFinite S
  have hS : T.system.toStructure.IsClosed S :=
    T.system.weak_support_closed D T.isPartite.1 A α
  exact T.system.clippedUSize_iff_wholeMaskUSize_of_closed hPos S hS n

end StructuralRamsey.FunctionalPartite.EHN

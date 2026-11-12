import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019
import PartiteConstruction.Functional.NativePartialClosure

/-!
# Track B: one-way U-size transport on arbitrary exact weak cuts

Whole-fibre weak deletion is no stronger as a generating operation
than clipping on the same carrier. The literal identity map is an
original-2019 source-defined homomorphism from whole-fibre weak to
clipped weak; it need not reflect undefined applications. Hence
minimum-generator size can only decrease under clipping.

The source theorem applies to arbitrary Option(Set) fibres, including
defined-empty values, nullaries, repeated inputs and partially
retained multivalued values. After faithful native conversion, this
yields the one direction between the different ambient 2019 USize
presentations that holds on EVERY exact weak test.

Finally the real EHN source-defined part projection decreases WHOLE
ambient USize on its exact image. Compose with the one-way dictionary
there to bound CLIPPED USize of the exact projected control image.
No closure hull, full projection, strict B-tree completion, or class-
local H-valued completion is asserted.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- On the SAME exact weak carrier S, the identity is an original
source-defined partial homomorphism from whole-fibre deletion to
clipped deletion. An application deleted in the whole convention
may be present after clipping; there is NO domain reflection. -/
theorem wholeWeakInduce_to_clipped_originalPartial
    (A : PartialSetStructure L V) (S : Set V) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce A S) (weakInduce A S) (id : S → S) := by
  classical
  constructor
  · intro R xs hR
    exact hR
  · intro F xs U hU
    change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) =
      some U at hU
    obtain ⟨T, hT, hTS, rfl⟩ :=
      (wholeWeakValue_eq_some_iff S _ U).mp hU
    change weakValue S (A.func F (Subtype.val ∘ xs)) =
      some (Structure.imageSet id {y : S | y.1 ∈ T})
    rw [hT, weakValue_of_subset S T hTS]
    simp [Structure.imageSet]

/-- Whole-fibre deletion can require MORE generators, but never fewer,
than clipping the SAME weak test. Proof is on the genuine Option(Set)
structures and retains defined-empty versus undefined domains. -/
theorem wholeWeakGeneratedByAtMost_implies_clipped
    (A : PartialSetStructure L V) (S : Set V) (n : ℕ)
    (hGen : (wholeWeakInduce A S).GeneratedByAtMost n) :
    (weakInduce A S).GeneratedByAtMost n :=
  hGen.of_surjective_originalPartialHomomorphism
    (wholeWeakInduce_to_clipped_originalPartial A S)
    (fun x => ⟨x, rfl⟩)

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]

/-- The sharp universally valid ONE-WAY comparison between canonical
2019 ambient USize presentations of the SAME exact weak carrier.
Whole-mask/whole-fibre rank at most n implies split-output/clipped
rank at most n, with no no-partial-fibre or closed-cut hypothesis.

The converse is false for transversal multivalued fibres. This is
only a rank implication; canonical tagged languages are not equal. -/
theorem System.wholeMaskUSize_le_implies_clippedUSize_le
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (S : Set V) [Fintype S] (n : ℕ)
    (hWhole :
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) ≤ n) :
      USize (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) ≤ n := by
  have hWholeGen :
      (wholeWeakInduce B.toStructure.toNonemptyPartial S).GeneratedByAtMost n :=
    (B.toStructure.toNonemptyPartial.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      B.part hPos B.toNonemptyPartial_fibreTransversal S n).mpr hWhole
  have hClippedGen :
      (B.toStructure.toNonemptyPartial.weakInduce S).GeneratedByAtMost n :=
    B.toStructure.toNonemptyPartial.wholeWeakGeneratedByAtMost_implies_clipped
      S n hWholeGen
  have hFaithful :
      ((B.toStructure.weakInduce S).toNonemptyPartial).GeneratedByAtMost n := by
    rw [Structure.toNonemptyPartial_weakInduce_commute]
    exact hClippedGen
  have hNative :
      (B.toStructure.weakInduce S).GeneratedByAtMost n :=
    ((B.toStructure.weakInduce S).toNonemptyPartial_generatedByAtMost_iff n).mp
      hFaithful
  exact (B.weakGeneratedByAtMost_iff_outputTaggedUSize_le hPos S n).mp hNative

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Exact-image ONE-WAY transfer for the ACTUAL EHN stage:
if the source weak test S has whole-mask ambient 2019 generator rank
at most n, then the literal control image part '' S has CLIPPED
split-output ambient 2019 rank at most n as well.

This uses only the genuine weak EHN projection; no ProjectionHom,
image closure, or replacement of S is used. The inverse implication
is false without an additional complete-fibre retention hypothesis. -/
theorem Stage.exactProjectedClippedUSize_le_of_wholeSource
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) [Fintype S]
    [Fintype (Structure.imageSet T.system.part S)]
    (n : ℕ)
    (hSource :
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
            T.system.part)).induce S) ≤ n) :
    USize (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        ((transversal D).splitOutputParts).toStructure.patternGraph).induce
          (Structure.imageSet T.system.part S)) ≤ n := by
  have hImage :
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          ((D.toNonemptyPartial).wholeMaskPatternGraph
            (fun p : P => p))).induce
              (Structure.imageSet T.system.part S)) ≤ n :=
    (T.inducedAmbientWholeMaskUSize_le hPos S).trans hSource
  exact (transversal D).wholeMaskUSize_le_implies_clippedUSize_le
    hPos (Structure.imageSet T.system.part S) n hImage

end StructuralRamsey.FunctionalPartite.EHN

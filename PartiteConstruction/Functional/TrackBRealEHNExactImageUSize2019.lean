import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.NativeWholePartClosure
import PartiteConstruction.Functional.WholeMaskWholeWeakImageRank2019
import PartiteConstruction.Functional.EHNStage

/-!
# Track B: original EHN projection gives exact 2019 USize monotonicity

The existing `Structure.IsEHNHomomorphismEmbedding.toOriginalPartial`
is precisely the ORIGINAL 2019 source-defined, whole-value partial
homomorphism law. Native set-valued structures encode undefined inputs
by EMPTY output sets, so `Structure.toNonemptyPartial` turns them
into genuine Option(Set) operations WITHOUT inventing defined-empty
tuples.

We show that this original partial law preserves all source-defined
Option(Set) fibres under this faithful conversion, then apply the
verified ambient whole-mask weak-image USize theorem. The result
covers the ACTUAL EHN weak part projection, not just a full projection.

The exact weak source carrier is S, the exact target weak carrier
is `B.part '' S` (not its ambient closure); USize is minimum number
of generators, not cardinality of a function-generated hull.

No reflection of undefined inputs or total-fibre homomorphism
equation is assumed, and no strict mixed-root B-tree is produced.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- The ORIGINAL native 2019 source-defined homomorphism becomes the
genuine `Option(Set)` source-defined homomorphism on the faithful
nonempty-domain interpretation, on exactly the same source/target
carriers and vertex map.

In particular, the target may have a defined function input on a
source-undefined input: no false reflection of undefinedness is used.
Every source-defined value must map onto the ENTIRE target value set. -/
theorem IsOriginalPartialHomomorphism.toNonemptyPartial
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      A.toNonemptyPartial B.toNonemptyPartial f := by
  classical
  constructor
  · exact hf.1
  · intro F x S hValue
    by_cases hNonempty : (A.func F x).Nonempty
    · have hSource : A.func F x = S := by
        change
          (if (A.func F x).Nonempty then some (A.func F x)
            else none) = some S at hValue
        simpa [hNonempty] using hValue
      have hMap : imageSet f (A.func F x) =
          B.func F (f ∘ x) := hf.2 F x hNonempty
      have hTargetNonempty :
          (B.func F (f ∘ x)).Nonempty := by
        obtain ⟨a, ha⟩ := hNonempty
        have hImage : f a ∈ imageSet f (A.func F x) :=
          ⟨a, ha, rfl⟩
        rw [hMap] at hImage
        exact ⟨f a, hImage⟩
      change
        (if (B.func F (f ∘ x)).Nonempty then
          some (B.func F (f ∘ x)) else none) =
        some (imageSet f S)
      simp only [if_pos hTargetNonempty]
      exact congrArg some (hMap.symm.trans
        (congrArg (imageSet f) hSource))
    · change
        (if (A.func F x).Nonempty then
          some (A.func F x) else none) = some S at hValue
      simp [hNonempty] at hValue

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable [Fintype P]

/-- Every genuine EHN `WeaklyPartiteOver` projection has the exact
original-2019 partial homomorphism law on its Option(Set) source and
control structures, WITHOUT a full total-fibre projection. -/
theorem System.weaklyPartite_toNonemptyPartial_originalHom
    (B : System L P V) (A : Structure L P)
    (hB : B.WeaklyPartiteOver A) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      B.toStructure.toNonemptyPartial A.toNonemptyPartial B.part :=
  (hB.toOriginalPartial.1).toNonemptyPartial

/-- The exact image of any literal weak EHN test S has ambient OLD
2019 U-generator size at most that of S, even when the projection
identifies source vertices and even though source-undefined
function inputs may become defined in the common control.

Both induced ambient graphs retain their ORIGINAL domain masks,
and the target image is literally `B.part '' S`, not a closure
of that set. Positive primitive function arity, transversal
outputs and finite source/part carriers are the checked hypotheses.
-/
theorem System.weaklyPartite_inducedAmbientWholeMaskUSize_le
    (B : System L P V) [Finite V]
    (A : Structure L P)
    (hB : B.WeaklyPartiteOver A)
    (hPos : L.PositiveFuncArity)
    (S : Set V) [Fintype S]
    [Fintype (Structure.imageSet B.part S)] :
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((A.toNonemptyPartial).wholeMaskPatternGraph
          (fun p : P => p))).induce (Structure.imageSet B.part S)) ≤
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((B.toStructure.toNonemptyPartial).wholeMaskPatternGraph
          B.part)).induce S) := by
  have hf : PartialSetStructure.IsOriginalPartialHomomorphism
      B.toStructure.toNonemptyPartial A.toNonemptyPartial B.part :=
    B.weaklyPartite_toNonemptyPartial_originalHom A hB
  have hTrB : FibreTransversal
      B.toStructure.toNonemptyPartial B.part :=
    B.toNonemptyPartial_fibreTransversal
  have hTrA : FibreTransversal A.toNonemptyPartial
      (fun p : P => p) :=
    (transversal A).toNonemptyPartial_fibreTransversal
  exact hf.inducedAmbientWholeMaskUSize_le
    B.part (fun p : P => p) hTrB hTrA hPos S

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Literal current EHN Stage projection is sufficient to bound the
2019 ambient U-generator rank of EVERY exact weak image of S.

No full `ProjectionHom` is required: use the Stage's STORED
`isPartite` EHN invariant, whose original-2019 source-defined
partial-fibre law is preserved by the faithful Option(Set) lift.
The image carrier remains exactly `T.system.part '' S`. -/
theorem Stage.inducedAmbientWholeMaskUSize_le
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) [Fintype S]
    [Fintype (Structure.imageSet T.system.part S)] :
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((D.toNonemptyPartial).wholeMaskPatternGraph
          (fun p : P => p))).induce
            (Structure.imageSet T.system.part S)) ≤
    USize (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
          T.system.part)).induce S) :=
  T.system.weaklyPartite_inducedAmbientWholeMaskUSize_le
    D T.isPartite hPos S

end StructuralRamsey.FunctionalPartite.EHN

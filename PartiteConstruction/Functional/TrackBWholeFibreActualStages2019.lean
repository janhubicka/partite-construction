import PartiteConstruction.Functional.Induced
import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.NativeWholePartClosure
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019

/-!
# Track B: genuine whole-fibre Option(Set) 2019 source dictionary on actual stages

The native Hales--Jewett construction uses total set-valued functions,
interpreting an empty fibre as undefined. The faithful
`Structure.toNonemptyPartial` transformation exposes the original
definedness as Option(Set), with NO invented defined-empty values.

After whole-fibre weak deletion on any exact Test, native vertex closure
and minimum generator size correspond to U-closure and USize of the
AMBIENT 2019 OLD complete-mask tagged source on Test.

These are independent of the clipped `Structure.weakInduce`
correspondence. In particular a multivalued fibre partly meeting Test
can contribute surviving clipped outputs but is DELETED completely in
this whole-fibre model. The two USize predicates are not asserted equal.

All source Stage carriers are original; no closure hull is substituted
for Test. This does not construct strict B-tree target completions.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The genuine whole-fibre partial-function weak restriction of an
ACTUAL native functional Stage has the same weak closed-subset
predicate and minimal generator-size bound as its AMBIENT complete-mask
2019 tagged source on the identical Test carrier.

This uses the independent `Option(Set)` language and its full domain
masks; it is NOT the clipped `weakInduce` structure. -/
theorem Stage.exactWholeWeakUClosureAndGeneratorRank
    (T : Stage K D)
    (hPos : L.PositiveFuncArity)
    (Test : Set T.Carrier) [Fintype Test] (n : ℕ) :
    (∀ Q : Set Test,
      (wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).IsClosed Q ↔
        IsUSubstructure (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
              T.system.part)).induce Test) Q) ∧
    ((wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          ((T.system.toStructure.toNonemptyPartial).wholeMaskPatternGraph
            T.system.part)).induce Test) ≤ n) := by
  let A := T.system.toStructure.toNonemptyPartial
  have hTrans : FibreTransversal A T.system.part :=
    T.system.toNonemptyPartial_fibreTransversal
  constructor
  · intro Q
    exact A.wholeWeakIsClosed_iff_inducedAmbientTagUSubstructure
      T.system.part hPos hTrans Test Q
  · exact A.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      T.system.part hPos hTrans Test n

/-- The SAME whole-fibre 2019 exact-carrier dictionary applies to the
ACTUAL native Hales--Jewett coordinate power, not a surrogate tag
power. Each primitive partial value is a COMPLETE multivalued fibre,
retained only when every one of its outputs lies in Test. -/
theorem nativePower_exactWholeWeakUClosureAndGeneratorRank
    (B : System L P V) [Finite V]
    (N : ℕ) (hPos : L.PositiveFuncArity)
    (Test : Set (Induced.Vertex B N)) [Fintype Test] (n : ℕ) :
    (∀ Q : Set Test,
      (wholeWeakInduce
        ((Induced.power B N).toStructure.toNonemptyPartial) Test).IsClosed Q ↔
        IsUSubstructure (L.wholeMaskClosureRules P)
          ((wholeMaskTagExpansion
            (((Induced.power B N).toStructure.toNonemptyPartial)
              .wholeMaskPatternGraph (Induced.power B N).part)).induce
                Test) Q) ∧
    ((wholeWeakInduce
        ((Induced.power B N).toStructure.toNonemptyPartial) Test).GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (((Induced.power B N).toStructure.toNonemptyPartial)
            .wholeMaskPatternGraph (Induced.power B N).part)).induce
              Test) ≤ n) := by
  let Source := Induced.power B N
  let A := Source.toStructure.toNonemptyPartial
  have hTrans : FibreTransversal A Source.part :=
    Source.toNonemptyPartial_fibreTransversal
  constructor
  · intro Q
    exact A.wholeWeakIsClosed_iff_inducedAmbientTagUSubstructure
      Source.part hPos hTrans Test Q
  · exact A.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
      Source.part hPos hTrans Test n

end StructuralRamsey.FunctionalPartite.EHN

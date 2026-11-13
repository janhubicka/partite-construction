import PartiteConstruction.Functional.TrackBDualUSizeClosedSupport2019
import PartiteConstruction.Functional.TrackBOneWayClosureHull2019

/-!
# Track B: equality of BOTH exact 2019 closure hulls on compatible cuts

The source-side Track B validation already proves:

* for every literal weak S and seed Q, whole-fibre 2019 OLD-mask
  UClosureHull is contained in clipped output-part-split UClosureHull;
* on a cut S with NO PARTIALLY RETAINED function value, the actual
  clipped native partial presentation equals the whole-fibre
  Option(Set) weak presentation on exactly S.

We now use the latter equality, and the two independently verified
canonical 2019 closure dictionaries, to get exact EQUALITY of the
two UClosureHull operations for every seed Q on such a cut S.

The two canonical tagged relational languages are different; this is
only an equality of their *induced vertex closure operators* on the
same original carrier and initial seed. It implies, but is stronger
than, the previously proved equivalence of minimum-generator USize
bounds. The result is specialized to the selected function-closed
A-support of any actual EHN Stage and to the literal closed image
of a full attached B-copy.

No equality is claimed on arbitrary weak cuts: the genuine finite
multivalued rank-gap regression in Track B forbids that extension.
No H-valued local completion or strict mixed-root B-tree is asserted.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V : Type v} [Fintype P]

/-- EQUALITY of the two separately tagged 2019 vertex-closure
operations on exactly the same S and Q, assuming no native fibre
meets S without lying entirely in S.

The actual tagged relational languages remain distinct. -/
theorem System.wholeMaskUClosureHull_eq_clipped_of_noPartial
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (S : Set V)
    (hNo : NoPartiallyRetainedValues B.toStructure.toNonemptyPartial S)
    (Q : Set S) :
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) Q := by
  have hEqual :
      (B.toStructure.weakInduce S).toNonemptyPartial =
        wholeWeakInduce B.toStructure.toNonemptyPartial S :=
    (Structure.toNonemptyPartial_weakInduce_eq_whole_iff
      B.toStructure S).mpr hNo
  have hWhole :=
    B.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      B.part hPos B.toNonemptyPartial_fibreTransversal S Q
  have hClipped :=
    B.weakFunctionClosure_eq_outputTaggedUClosureHull hPos S Q
  calc
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q
        = (wholeWeakInduce B.toStructure.toNonemptyPartial S).functionClosure Q :=
          hWhole.symm
    _ = ((B.toStructure.weakInduce S).toNonemptyPartial).functionClosure Q := by
      rw [hEqual]
    _ = (B.toStructure.weakInduce S).functionClosure Q :=
      (B.toStructure.weakInduce S).toNonemptyPartial_functionClosure Q
    _ = UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) Q :=
      hClipped

/-- On any genuinely function-closed native cut S the two canonical
2019 induced U-closure hulls agree for EVERY seed Q on that exact S.
No finite-generator bound, target completion, or closure inflation. -/
theorem System.wholeMaskUClosureHull_eq_clipped_of_closed
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Q : Set S) :
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) Q := by
  have hClosed : B.toStructure.toNonemptyPartial.IsClosed S :=
    (Structure.toNonemptyPartial_isClosed_iff B.toStructure S).mpr hS
  have hNo : NoPartiallyRetainedValues
      B.toStructure.toNonemptyPartial S := by
    intro F xs U hValue
    left
    exact hClosed F (Subtype.val ∘ xs) U (fun i => (xs i).2) hValue
  exact B.wholeMaskUClosureHull_eq_clipped_of_noPartial hPos S hNo Q

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P U : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The actual EHN selected closed support for one Picture attachment
has identical whole-mask and clipped 2019 U-closures for EVERY
literal seed Q on that exact support. -/
theorem Stage.selectedSupport_dualUClosureHull_eq
    (T : Stage K D)
    (A : Structure L U) (α : Structure.Embedding A D)
    (hPos : L.PositiveFuncArity)
    (Q : Set (T.system.support α.toFunctionEmbedding)) :
    let S := T.system.support α.toFunctionEmbedding
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
          T.system.part)).induce S) Q =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q := by
  let S := T.system.support α.toFunctionEmbedding
  have hS : T.system.toStructure.IsClosed S :=
    T.system.weak_support_closed D T.isPartite.1 A α
  exact T.system.wholeMaskUClosureHull_eq_clipped_of_closed hPos S hS Q

/-- Every FULL native partite B-copy in an actual EHN Stage has
function-closed range, so any chosen seed Q inside that exact copy
range has the SAME whole-mask and clipped tagged 2019 closure hull.
The map is the real full-copy map; no synthetic carrier is used. -/
theorem Stage.fullCopyRange_dualUClosureHull_eq
    (T : Stage K D)
    {V : Type v} (B : System L P V)
    (copy : FunctionalPartite.Embedding B T.system)
    (hPos : L.PositiveFuncArity)
    (Q : Set (Set.range copy.toEmbedding.toFun)) :
    let S := Set.range copy.toEmbedding.toFun
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
          T.system.part)).induce S) Q =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q := by
  let S := Set.range copy.toEmbedding.toFun
  have hS : T.system.toStructure.IsClosed S :=
    copy.toEmbedding.range_isClosed
  exact T.system.wholeMaskUClosureHull_eq_clipped_of_closed hPos S hS Q

end StructuralRamsey.FunctionalPartite.EHN

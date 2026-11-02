import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Functional.TrackBHeterogeneousTaggedPreimage2019
import PartiteConstruction.Functional.EHNStage

/-!
# Track B: true EHN weak-projection HJ line maps preserve full 2019 tags

The actual functional EHN / iterated Picture uses
`System.WeaklyPartiteOver`, NOT the stronger global full
`System.ProjectionHom`. Nevertheless the Hales--Jewett
`Induced.weak_lineEmbedding` is a genuine FULL functional partite
embedding (verified in WeakInduced.lean): a parameter coordinate and
output transversality give equality of complete function fibres.

Consequently its exact original vertex map gives a FULL canonical
2019 OLD equality-pattern and fresh-root tagged embedding on every
literal weak preimage. Ambient domain/root masks are inherited
from the original source and must not be recomputed from the
clipped or whole-fibre intrinsic weak structure.

This is a real EHN interface, not an artificial strong-projection
assumption. No source vertices are added or closed, no arbitrary
weak induced functional inclusion is declared full, and no strict
mixed-root target B-tree completion is asserted.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- Every ACTUAL HJ line under only the EHN weak homomorphism
projection is a full native function embedding, and therefore
a full OLD equality-pattern and COMPLETE fresh 2019 U-root
embedding on all exact ambient-induced weak preimages.

The vertex map is literally the original `weak_lineMap`;
there is NO part/fibre-surjectivity requirement on the EHN
projection itself. -/
theorem weak_lineEmbedding_taggedWeakPreimage
    (A : Structure L P) (B : System L P V)
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N)) :
    let e := (weak_lineEmbedding hB W).splitOutputParts.toEmbedding
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce
          (e.toFun ⁻¹' Test))
      ((patternTagExpansion
        ((power B N).splitOutputParts).toStructure.patternGraph).induce
          Test)) := by
  let e := (weak_lineEmbedding hB W).splitOutputParts.toEmbedding
  exact ⟨e.heteroTaggedPatternWeakPreimage Test⟩

/-- Direct specialization to the genuine EHN invariant.
`WeaklyPartiteOver` entails only the prescribed EHN weak
projection; its full LINE embeddings carry canonical OLD
domain/output and fresh complete-root records on every Test. -/
theorem weaklyPartite_lineEmbedding_taggedWeakPreimage
    (A : Structure L P) (B : System L P V)
    (hB : B.WeaklyPartiteOver A)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N)) :
    let e := (weak_lineEmbedding hB.1 W).splitOutputParts.toEmbedding
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce
          (e.toFun ⁻¹' Test))
      ((patternTagExpansion
        ((power B N).splitOutputParts).toStructure.patternGraph).induce
          Test)) := by
  exact weak_lineEmbedding_taggedWeakPreimage A B hB.1 W Test

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- An actual finite EHN Stage, with only its genuine stored
`isPartite : WeaklyPartiteOver` invariant, has full canonical
ambient 2019 tagged weak-preimage maps along each native HJ line
of the stage's own coordinate power.

This references the REAL stage and its REAL weak line maps,
rather than requiring `ProjectionHom` or constructing another
Ramsey witness. -/
theorem Stage.taggedWeakLinePreimage
    (T : Stage K D)
    {N : ℕ} (W : Line (Induced.Letter D T.system) N)
    (Test : Set (Induced.Vertex T.system N)) :
    let e := (Induced.weak_lineEmbedding T.isPartite.1 W)
      .splitOutputParts.toEmbedding
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (T.system.splitOutputParts).toStructure.patternGraph).induce
          (e.toFun ⁻¹' Test))
      ((patternTagExpansion
        ((Induced.power T.system N).splitOutputParts).toStructure.patternGraph).induce
          Test)) := by
  exact Induced.weak_lineEmbedding_taggedWeakPreimage
    D T.system T.isPartite.1 W Test

end StructuralRamsey.FunctionalPartite.EHN

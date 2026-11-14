import PartiteConstruction.Functional.TrackBOneWayWeakMapNaturality2019
import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019
import PartiteConstruction.Functional.TrackBWholeFibreActualStages2019

/-!
# Appendix Track B: exact whole-fibre U-closure naturality of FULL copy maps

An original-2019 *source-defined* partial homomorphism f merely sends
the source closure INTO target closure. Equality is false in general
because target operations can be defined on source-undefined inputs.

For a genuinely FULL independent-domain Option(Set) embedding e,
the range of any source function-CLOSED subset is function-closed in
the target: the closed induced source inclusion composes with e to a
full embedding, whose range is closed. Hence every generated closure
is taken ONTO the closure of its exact image seed, not merely into it.
This argument respects nullary functions and defined-empty fibres.

For ANY literal target weak test Test, the verified full whole-fibre
weak restriction of e on e⁻¹(Test) is again full. Thus this equality
of closure IMAGE holds on the exact weak source and target carriers
even if Test is not function-closed.

Specialized to an ACTUAL EHN Stage full attached-copy embedding, and
the ACTUAL Hales--Jewett line full embedding into native coordinate
power, this identifies whole-fibre weak-generated closure images.
No weak EHN part projection is upgraded to a full homomorphism.
No tagged-language isomorphism or target class-local completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A FULL genuine-partial embedding sends an arbitrary function-closed
source subset to a function-closed target subset. This fails for a
merely original source-defined map at source-undefined inputs. -/
theorem Embedding.image_isClosed_of_isClosed
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B)
    (S : Set V) (hS : A.IsClosed S) :
    B.IsClosed (Structure.imageSet e.toFun S) := by
  let inc := closedInclusion A S hS
  let emb := e.comp inc
  have hRange : B.IsClosed (Set.range emb.toFun) :=
    emb.range_isClosed
  have hEq :
      Set.range emb.toFun = Structure.imageSet e.toFun S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hEq]
  exact hRange

/-- FULL embeddings preserve the generated closure EXACTLY on
the vertex image of any seed. The image itself is a closed target
subset, so the target closure cannot generate new outside vertices. -/
theorem Embedding.image_functionClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (Q : Set V) :
    Structure.imageSet e.toFun (A.functionClosure Q) =
      B.functionClosure (Structure.imageSet e.toFun Q) := by
  apply Set.Subset.antisymm
  · exact e.toOriginalPartialHom.image_functionClosure_subset Q
  · have hImg : B.IsClosed
        (Structure.imageSet e.toFun (A.functionClosure Q)) :=
      e.image_isClosed_of_isClosed _ (A.functionClosure_isClosed Q)
    apply B.functionClosure_least hImg
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, A.subset_functionClosure Q hx, rfl⟩

/-- The *actual exact preimage* of any target weak test under a FULL
genuine partial embedding inherits equality of WHOLE weak closure
images, with the true restricted map. Neither carrier is enlarged by
closing it; full domain reflection handles missing input profiles. -/
theorem Embedding.wholeWeakPreimage_imageClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B)
    (Test : Set W) (Q : Set (e.toFun ⁻¹' Test)) :
    Structure.imageSet (restrictMap e.toFun Test)
      ((wholeWeakInduce A (e.toFun ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap e.toFun Test) Q) :=
  (e.wholeWeakRestrictToPreimage Test).image_functionClosure_eq Q

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- For the literal FULL attached B-copy of an ACTUAL EHN Stage T,
the whole-fibre weak closure image along its exact preimage of any
nonclosed weak Test equals the weak closure of the image seed IN Test.
No functional target B-tree completion, class membership or full
EHN stage part projection is claimed. -/
theorem Stage.fullCopy_wholeWeakPreimage_imageClosure_eq
    (T : Stage K D)
    (B : System L P V)
    (copy : FunctionalPartite.Embedding B T.system)
    (Test : Set T.Carrier)
    (Q : Set (copy.toEmbedding.toFun ⁻¹' Test)) :
    Structure.imageSet (restrictMap copy.toEmbedding.toFun Test)
      ((wholeWeakInduce B.toStructure.toNonemptyPartial
        (copy.toEmbedding.toFun ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce T.system.toStructure.toNonemptyPartial Test).functionClosure
      (Structure.imageSet (restrictMap copy.toEmbedding.toFun Test) Q) := by
  exact (copy.toEmbedding.toNonemptyPartial).wholeWeakPreimage_imageClosure_eq
    Test Q

end StructuralRamsey.FunctionalPartite.EHN

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- The ACTUAL Hales--Jewett full line map satisfies equality of
whole-fibre closure images on an arbitrary literal weak Test in the
genuine native coordinate power. The EHN projection is only weak. -/
theorem weakLine_wholeWeakPreimage_imageClosure_eq
    (A : Structure L P)
    (B : System L P V)
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N))
    (Q : Set (((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test)) :
    Structure.imageSet
      (restrictMap ((weak_lineEmbedding hB W).toEmbedding.toFun) Test)
      ((wholeWeakInduce B.toStructure.toNonemptyPartial
        (((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce (power B N).toStructure.toNonemptyPartial Test).functionClosure
      (Structure.imageSet
        (restrictMap ((weak_lineEmbedding hB W).toEmbedding.toFun) Test) Q) := by
  exact ((weak_lineEmbedding hB W).toEmbedding.toNonemptyPartial)
    |>.wholeWeakPreimage_imageClosure_eq Test Q

end StructuralRamsey.FunctionalPartite.Induced

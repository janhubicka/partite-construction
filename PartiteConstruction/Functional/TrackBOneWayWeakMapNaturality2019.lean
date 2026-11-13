import PartiteConstruction.Functional.TrackBOneWayWeakUSize2019
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.WeakInduced
import PartiteConstruction.Functional.EHNStage

/-!
# Track B: naturality of source-defined whole-to-clipped maps

For a FULL genuine Option(Set) embedding e : A ↪ B, the original
2019 whole-fibre weak restriction on the EXACT preimage e⁻¹(Test)
embeds fully into the whole-fibre weak restriction of B on Test.
The identity whole→clipped map on the SAME target Test is only a
source-defined homomorphism, not a full embedding. Their composition
is therefore a precise original-partial homomorphism on the SAME
vertex map and exact weak carriers, with no closure hull.

Apply the result to literal full native attached-copy embeddings in
an actual finite EHN Stage, and separately to the ACTUAL weak HJ
line embeddings into the genuine native coordinate power. The
underlying weak EHN projection never needs to be a full
ProjectionHom. No claim identifies induced ambient OLD-tagged tests
with intrinsic whole-fibre partial structures.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A FULL independent-domain partial embedding is in particular an
original-2019 source-defined homomorphism; reflection of undefined
inputs is discarded, not assumed for the following weak maps. -/
theorem Embedding.toOriginalPartialHom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) :
    IsOriginalPartialHomomorphism A B e.toFun := by
  constructor
  · intro R xs hRel
    exact (e.map_rel_iff R xs).mpr hRel
  · intro F xs U hU
    have h := e.map_func F xs
    simp only [hU, Option.map_some] at h
    exact h.symm

/-- The full-embedding square followed by the original source-defined
whole→clipped comparison. On the exact e⁻¹(Test) the map is literally
the restricted original e, with no inserted vertices or closure. -/
theorem Embedding.wholeWeakPreimage_to_clippedHom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (Test : Set W) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce A (e.toFun ⁻¹' Test))
      (weakInduce B Test)
      (restrictMap e.toFun Test) := by
  have hFull :=
    (e.wholeWeakRestrictToPreimage Test).toOriginalPartialHom
  have hClip := wholeWeakInduce_to_clipped_originalPartial B Test
  exact hClip.comp hFull

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Every literal full attached-copy map B↪T in an ACTUAL functional
EHN Stage induces the original-2019 source-defined partial
homomorphism on exact whole-fibre weak copy preimages, landing in
the clipped weak stage test. Neither S nor its image is closed. -/
theorem Stage.fullCopy_wholeWeakPreimage_to_clippedHom
    (T : Stage K D)
    (B : System L P V)
    (copy : FunctionalPartite.Embedding B T.system)
    (Test : Set T.Carrier) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce
        B.toStructure.toNonemptyPartial
          (copy.toEmbedding.toFun ⁻¹' Test))
      (PartialSetStructure.weakInduce
        T.system.toStructure.toNonemptyPartial Test)
      (PartialSetStructure.restrictMap copy.toEmbedding.toFun Test) := by
  exact (copy.toEmbedding.toNonemptyPartial)
    .wholeWeakPreimage_to_clippedHom Test

end StructuralRamsey.FunctionalPartite.EHN

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- The ACTUAL full Hales--Jewett LINE map under only the weak EHN
projection carries its exact whole-fibre weak preimage by an original
source-defined map into the clipped weak native power test.

This is a same-line/same-Test map, not an arbitrary EHN projection or
an isomorphism of the two canonical ambient OLD tagged languages. -/
theorem weakLine_wholeWeakPreimage_to_clippedHom
    (A : Structure L P)
    (B : System L P V)
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N)) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce B.toStructure.toNonemptyPartial
        (((weak_lineEmbedding hB W).toEmbedding.toFun) ⁻¹' Test))
      (weakInduce (power B N).toStructure.toNonemptyPartial Test)
      (restrictMap ((weak_lineEmbedding hB W).toEmbedding.toFun) Test) := by
  exact ((weak_lineEmbedding hB W).toEmbedding.toNonemptyPartial)
    .wholeWeakPreimage_to_clippedHom Test

end StructuralRamsey.FunctionalPartite.Induced

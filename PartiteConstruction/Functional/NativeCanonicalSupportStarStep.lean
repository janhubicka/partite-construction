import PartiteConstruction.Functional.NativeClosedMappedAnchor

/-!
# A native Picture star uses the original selected-support labels

The old 2019 functional Hales--Jewett Picture attaches many old-stage
copies to ONE original power core.  When a test becomes mixed, its exact
closed common separator is contained in the tested original-core anchor.

The previous mapped-anchor theorem returned an embedding of that anchor
back into the original core.  Here we prove the stronger equality on
the actual separator: that embedding agrees POINTWISE with the chosen
old-stage selected-support map.  Therefore the copied-side relative
extension can be requested over the fixed canonical support labels
without choosing a new target-side root map at each attachment.

The relative old-copy extension still has to be constructed in the
genuinely mixed, multi-generated maximal rank case.  The theorem below
does not silently turn a partial original-2019 map into a total-fibre
homomorphism or add closure vertices.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W X VB G : Type v}

/-- In a genuine UnitAttachD step whose support is embedded through the
original HJ core, the map of the exact closed root BACK to that core is
literally the selected support embedding on the source root.

Thus an old-copy relative completion may be stated with the single
canonical root q after supportIn and pb.commonMap, exactly as in the
published two-case Picture induction.  This is not an existence theorem
for the relative old-copy witness at hard multi-generated separators. -/
theorem closedTest_originalPartial_star_step_with_selected_support
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (OriginalCore : Structure L X)
    (coreIn : Structure.Embedding OriginalCore D.toStructure)
    (supportIn : Structure.Embedding
      (B.induce S hS).toStructure OriginalCore)
    (hFactor : ∀ s : S, f.toEmbedding s = coreIn (supportIn s))
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttachD B S hS D f).toStructure.IsClosed Test)
    (Base : Structure L VB) (Start : Structure L G)
    (q : X → G) :
    let pb := closedTestPullback B S hS D f Test hTest
    ∃ (T : Set pb.Left) (hT : pb.left.IsClosed T)
      (rootInAnchor : Structure.Embedding pb.common (pb.left.induce T hT))
      (toOriginal : Structure.Embedding
        (pb.left.induce T hT) OriginalCore),
      T = {x | pb.leftMap x ∈ Set.range coreIn} ∧
      (∀ x : pb.Common,
        (Structure.inclusion pb.left T hT) (rootInAnchor x) = pb.toLeft x) ∧
      (∀ x : T,
        pb.leftMap ((Structure.inclusion pb.left T hT) x) =
          coreIn (toOriginal x)) ∧
      (∀ x : pb.Common,
        toOriginal (rootInAnchor x) = supportIn (pb.commonMap x)) ∧
      (HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base (Structure.inclusion pb.left T hT)
          (q ∘ toOriginal) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base pb.toRight
          (q ∘ supportIn ∘ pb.commonMap) →
       HasOriginalPartialTreeExtensionCompletion
          (Start := Start) Base
          (pb.leftIn.comp (Structure.inclusion pb.left T hT))
          (q ∘ toOriginal)) := by
  let pb := closedTestPullback B S hS D f Test hTest
  obtain ⟨T, hT, rootInAnchor, toOriginal, hExact, hRoot, hMap, hStep⟩ :=
    closedTest_originalPartial_star_step_over_original_core
      B S hS D f OriginalCore coreIn supportIn hFactor
      Test hTest Base Start q
  have hSupportMap : ∀ x : pb.Common,
      toOriginal (rootInAnchor x) = supportIn (pb.commonMap x) := by
    intro x
    apply coreIn.injective
    calc
      coreIn (toOriginal (rootInAnchor x)) =
          pb.leftMap ((Structure.inclusion pb.left T hT) (rootInAnchor x)) :=
        (hMap (rootInAnchor x)).symm
      _ = pb.leftMap (pb.toLeft x) :=
        congrArg pb.leftMap (hRoot x)
      _ = f.toEmbedding (pb.commonMap x) := pb.common_left x
      _ = coreIn (supportIn (pb.commonMap x)) :=
        hFactor (pb.commonMap x)
  have hCanonical :
      ((q ∘ toOriginal) ∘ rootInAnchor) =
        (q ∘ supportIn ∘ pb.commonMap) := by
    funext x
    exact congrArg q (hSupportMap x)
  refine ⟨T, hT, rootInAnchor, toOriginal,
    hExact, hRoot, hMap, hSupportMap, ?_⟩
  intro hLeft hCopy
  have hCopyRelative : HasOriginalPartialTreeExtensionCompletion
      (Start := Start) Base pb.toRight
      ((q ∘ toOriginal) ∘ rootInAnchor) := by
    rw [hCanonical]
    exact hCopy
  exact hStep hLeft hCopyRelative

end StructuralRamsey.FunctionalPartite.Attachment

import PartiteConstruction.Ramsey.ClosureEmbeddedSourceClosed
import PartiteConstruction.Ramsey.ClosureSemiClosedFreeAmalgam

/-!
# A closed free amalgam of closed sides has a closed common root

U-irreducibility permits free decompositions with closed sides but
without an a priori closed common root.  However, if the ambient
WHOLE is also U-closed, the common root is necessarily U-closed.

Indeed, the image of each full U-closed side embedding into the
U-closed whole is a U-substructure.  The preimage of the right image
in the left side is exactly the range of the common root embedding,
by the *overlap* axiom of the free amalgam.  Relative closedness
pulls back along a full embedding, and an embedded U-substructure
of a U-closed left side is U-closed on the original root carrier.

Thus the remaining closure-hull decomposition obstruction in the
corrected 2019 proof is NOT common-root closedness.  The genuinely
hard issue is whether this U-closed root has a canonical H target
and whether the side completions use compatible maps to it.

This statement does NOT infer K-membership of the common root or
any compatible H-completions from closure alone.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E}
variable {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- For a U-CLOSED free amalgam of U-CLOSED sides, the common source
root is necessarily U-closed even though its closure was not an
assumption of the free-amalgam diagram.

The vertex sets and all embeddings stay unchanged. No hull or
auxiliary completion is formed. -/
theorem IsFreeAmalgam.root_isUClosed_of_closed_whole_and_sides
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hWhole : IsUClosed rules Whole)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right) :
    IsUClosed rules Root := by
  classical
  have hRightRange :
      IsUSubstructure rules Whole (Set.range iR) :=
    iR.range_isUSubstructure hRight hWhole
  have hOverlap :
      (iL ⁻¹' Set.range iR) = Set.range sL := by
    ext a
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨d, ha, _⟩ := (hFree.overlap a b).mp hb.symm
      exact ⟨d, ha.symm⟩
    · rintro ⟨d, hd⟩
      refine ⟨sR d, ?_⟩
      rw [← hd]
      exact (hFree.overlap (sL d) (sR d)).mpr
        ⟨d, rfl, rfl⟩
  have hRootRange :
      IsUSubstructure rules Left (Set.range sL) := by
    rw [← hOverlap]
    exact hRightRange.preimage_embedding iL
  exact sL.source_isUClosed_of_range_USubstructure
    hLeft hRootRange

end StructuralRamsey.RelStructure

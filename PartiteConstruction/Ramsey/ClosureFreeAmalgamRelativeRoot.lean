import PartiteConstruction.Ramsey.ClosureFreeAmalgamClosedRoot
import PartiteConstruction.Ramsey.ClosureUSubstructurePreimage

/-!
# Relative-side criterion for U-closed common roots

The exact free-overlap axiom identifies the preimage of the right-side
range in the left side with the range of the common root inclusion.

Therefore it is already enough that Left is intrinsically U-closed
and the Right range is a U-substructure of the whole free source:
the common Root is then intrinsically U-closed. Whole need NOT be
U-closed, and neither need Right. This is the correct sharp interface
for ambient weak tests with relatively closed sides.

The symmetric statement needs only Right closed and Left range
relatively U-closed. Both statements retain all original vertices,
relations and embeddings. They do not assert Root membership in
any Ramsey subclass K or existence of a compatible H completion.
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

/-- A U-closed LEFT side and a relatively U-closed RIGHT side range
force the common Root to be U-closed, with no ambient closedness
hypothesis on Whole and no intrinsic closedness of Right. -/
theorem IsFreeAmalgam.root_isUClosed_of_left_closed_right_relative
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hLeft : IsUClosed rules Left)
    (hRightRange : IsUSubstructure rules Whole (Set.range iR)) :
    IsUClosed rules Root := by
  classical
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
      exact ((hFree.overlap (sL d) (sR d)).mpr
        ⟨d, rfl, rfl⟩).symm
  have hRootRange :
      IsUSubstructure rules Left (Set.range sL) := by
    rw [← hOverlap]
    exact hRightRange.preimage_embedding iL
  exact sL.source_isUClosed_of_range_USubstructure
    hLeft hRootRange

/-- Symmetric relative-side criterion: RIGHT intrinsically U-closed,
and LEFT only relatively U-closed inside the whole free source. -/
theorem IsFreeAmalgam.root_isUClosed_of_right_closed_left_relative
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRight : IsUClosed rules Right)
    (hLeftRange : IsUSubstructure rules Whole (Set.range iL)) :
    IsUClosed rules Root :=
  hFree.swap.root_isUClosed_of_left_closed_right_relative
    hRight hLeftRange

end StructuralRamsey.RelStructure

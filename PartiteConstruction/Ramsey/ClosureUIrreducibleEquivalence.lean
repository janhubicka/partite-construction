import PartiteConstruction.Ramsey.ClosureRelativeIrreducibleWeakTest
import PartiteConstruction.Ramsey.ClosureEmbeddedSourceClosed

/-! # Two U-irreducibility notions coincide in U-closed ambient structures

For an arbitrary weak induced test, a free decomposition into
intrinsically U-closed sides is not the same as a free decomposition
into *relative* U-substructures.  There is, however, no ambiguity on
a genuinely U-closed ambient structure: Lemma 2.23(1), the relative
range lemma, and exact source-closedness transport make the two
notions equivalent.

The theorem does NOT extend to arbitrary non-U-closed weak tests.
Such tests remain governed by the relative side-localization theorem,
which must not be replaced by this equivalence outside its hypothesis.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U : Type v}

/-- For U-closed A, intrinsic-side and ambient-relative definitions
of U-irreducibility agree exactly (on A's original vertices). -/
theorem IsUClosed.uIrreducible_iff_relative
    {rules : ClosureDescription L}
    {A : RelStructure L U}
    (hA : IsUClosed rules A) :
    IsUIrreducible rules A ↔
      IsURelativelyIrreducible rules A := by
  constructor
  · intro hIntrinsic
    intro H E F Root Left Right sL sR iL iR hFree hSubLeft hSubRight
    have hLeftClosed : IsUClosed rules Left :=
      iL.source_isUClosed_of_range_USubstructure hA hSubLeft
    have hRightClosed : IsUClosed rules Right :=
      iR.source_isUClosed_of_range_USubstructure hA hSubRight
    exact hIntrinsic hLeftClosed hRightClosed hFree
  · intro hRelative
    intro H E F Root Left Right sL sR iL iR hLeftClosed hRightClosed hFree
    have hSubLeft : IsUSubstructure rules A (Set.range iL) :=
      iL.range_isUSubstructure hLeftClosed hA
    have hSubRight : IsUSubstructure rules A (Set.range iR) :=
      iR.range_isUSubstructure hRightClosed hA
    exact hRelative hFree hSubLeft hSubRight

end StructuralRamsey.RelStructure

import PartiteConstruction.Ramsey.ClosureSemiClosedFreeAmalgam
import PartiteConstruction.Ramsey.ClosureUSubstructurePreimage

/-! # Relative U-substructures of free amalgams and exact weak tests

A U-substructure is a vertex set that retains every *existing* closure
tuple whose designated root it contains.  It need not be a U-closed
structure in its own right when the ambient structure is U-semi-closed.

Over a U-closed common root, each side of a free amalgam of
U-semi-closed structures is a U-substructure of the whole.
This property restricts to *arbitrary* induced vertex tests without
taking a closure hull.  It does not assert U-closedness of these tests.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Existing closure tuples with roots in the left side cannot leave
that side.  Only U-semi-closedness of the other side is needed. -/
theorem IsFreeAmalgam.left_range_isUSubstructure
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hRight : IsUSemiClosed rules Right) :
    IsUSubstructure rules Whole (Set.range iL) := by
  intro rule hrule t ht hRange j
  have hLeftRoot :
      ∀ k : Fin rule.rootSize,
        ∃ a : E, t (k.castLE rule.rootLE) = iL a := by
    intro k
    obtain ⟨a, ha⟩ := hRange k
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ :=
    hFree.closureTuple_inLeft_of_root_inLeft_semi
      hRoot hRight rule hrule t ht hLeftRoot j
  exact ⟨a, ha.symm⟩

/-- Right-side analogue of the vertex-exact closure condition. -/
theorem IsFreeAmalgam.right_range_isUSubstructure
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left) :
    IsUSubstructure rules Whole (Set.range iR) :=
  hFree.swap.left_range_isUSubstructure hRoot hLeft

/-- Relative closure is inherited by arbitrary induced vertex tests.
Here the tested set S need not be a U-substructure, so the induced test
may have roots without their outputs.  No vertices are added. -/
theorem IsUSubstructure.induce_inter
    {rules : ClosureDescription L}
    {A : RelStructure L C} {T : Set C}
    (hT : IsUSubstructure rules A T)
    (S : Set C) :
    IsUSubstructure rules (A.induce S)
      {x : S | x.1 ∈ T} := by
  intro rule hrule t ht hRoot j
  have htA : A.rel rule.symbol (Subtype.val ∘ t) := ht
  have hRootA :
      ∀ k : Fin rule.rootSize,
        (Subtype.val ∘ t) (k.castLE rule.rootLE) ∈ T := by
    intro k
    exact hRoot k
  exact hT rule hrule (Subtype.val ∘ t) htA hRootA j

end StructuralRamsey.RelStructure

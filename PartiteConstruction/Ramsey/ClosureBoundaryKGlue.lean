import PartiteConstruction.Ramsey.ClosureRelativeMapGlue

/-! # Completion gluing across an ACTUAL closed K-boundary

A nonclosed weak test may be the free amalgam of two (possibly nonclosed)
sides with merely RELATIVELY U-closed ranges. If the common boundary
itself is a closed member of K, the two sides have K-completions and K
has strong amalgamation, the whole weak test has a K-completion.

No projected rank bound is needed for THIS gluing step, and neither the
source root nor sides are assumed to be induced closed hulls of a
projection. The only essential rank obstruction in the remaining
Theorem 2.18 increment is obtaining the side completions in the first
place, rather than gluing them once obtained.

Consequently any noncompletable weak free source with such a boundary
has a noncompletable proper side. This makes the minimal-bad-test logic
precise without pretending that that side has smaller U-size.
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

/-- Strong K amalgamation turns two independently completable
possibly-nonclosed sides into a completion of their free union,
provided the common root is itself a CLOSED K-member. Relative
closedness of the side ranges in the whole is the only source closure
condition; the source root need not be a substructure of a closed
ambient control. -/
theorem HasClosedUKCompletion.glue_over_closed_K_root_relative
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    [Finite H]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRelL : IsUSubstructure rules Whole (Set.range iL))
    (hRelR : IsUSubstructure rules Whole (Set.range iR))
    (hRootClosed : IsUClosed rules Root)
    (hRootK : K Root)
    (hLeft : HasClosedUKCompletion K rules Left)
    (hRight : HasClosedUKCompletion K rules Right) :
    HasClosedUKCompletion K rules Whole := by
  exact HasClosedUKCompletion.of_independent_projected_completions_relative
    rules hK hKIrr hFree hRelL hRelR
    Root hRootK hRootClosed
    Left Right
    (fun x : E => x) (fun x : F => x)
    ((Embedding.id Left).isClosedUHomomorphismEmbedding rules)
    ((Embedding.id Right).isClosedUHomomorphismEmbedding rules)
    (fun x : H => x) sL sR
    (fun _ => rfl) (fun _ => rfl)
    hLeft hRight

/-- Exact contrapositive for the minimal noncompletable test argument.
A free source which is NOT completable over a closed K-boundary
cannot have K-completable pieces on BOTH sides. This says nothing
about their absolute U-sizes: that remains the HJ history obligation. -/
theorem HasClosedUKCompletion.bad_side_of_bad_free_amalgam
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    [Finite H]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRelL : IsUSubstructure rules Whole (Set.range iL))
    (hRelR : IsUSubstructure rules Whole (Set.range iR))
    (hRootClosed : IsUClosed rules Root)
    (hRootK : K Root)
    (hBad : ¬ HasClosedUKCompletion K rules Whole) :
    (¬ HasClosedUKCompletion K rules Left) ∨
      (¬ HasClosedUKCompletion K rules Right) := by
  by_cases hLeft : HasClosedUKCompletion K rules Left
  · right
    intro hRight
    exact hBad (HasClosedUKCompletion.glue_over_closed_K_root_relative
      rules hK hKIrr hFree hRelL hRelR
      hRootClosed hRootK hLeft hRight)
  · exact Or.inl hLeft

end StructuralRamsey.RelStructure

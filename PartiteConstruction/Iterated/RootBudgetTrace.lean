import PartiteConstruction.Iterated.FinalAttachmentBudget

/-! # Finite traces of budgeted root attachments

A trace records the sum of the cardinalities of its irreducible gluing roots.
An initial local-tree bound n + cost yields bound n after the whole trace.
This is a budgeted finite-iteration theorem, not a uniform bound for the final
sparsening construction: the number of roots in that construction depends on
the witness, so paying for all roots in advance would be circular.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {VB X : Type v}

/-- A heterogeneous finite sequence of free attachments of copies of Base,
indexed by its accumulated root-size cost. -/
inductive RootBudgetTrace (Base : RelStructure L VB)
    (Start : RelStructure L X) :
    (Y : Type v) → RelStructure L Y → ℕ → Prop
  | nil : RootBudgetTrace Base Start X Start 0
  | snoc {Y H : Type v} [Finite Y] [Finite H]
      {C : RelStructure L Y} {Root : RelStructure L H} {cost : ℕ}
      (prev : RootBudgetTrace Base Start Y C cost)
      (hRoot : Root.Irreducible)
      (fCore : Embedding Root C) (fBase : Embedding Root Base) :
      RootBudgetTrace Base Start
        (FreeAmalgam.Vertex Root C Base fCore fBase)
        (FreeAmalgam.amalgam Root C Base fCore fBase)
        (cost + Nat.card H)

namespace RootBudgetTrace

variable {UA Y : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Start : RelStructure L X} {Target : RelStructure L Y} {cost : ℕ}

/-- Budgeted finite iteration needs only irreducibility of the control and of
the whole roots, not hereditary irreducibility of any structure. -/
theorem locallyTreeLike
    [Finite UA] [Finite VB]
    (trace : RootBudgetTrace Base Start Y Target cost)
    (hControl : Control.Irreducible) (n : ℕ)
    (hStart : LocallyTreeLike Control Base Start (n + cost)) :
    LocallyTreeLike Control Base Target n := by
  induction trace generalizing n with
  | nil => simpa using hStart
  | snoc prev hRoot fCore fBase ih =>
      apply LocallyTreeLike.freeAmalgam_rootBudget hControl hRoot n
      apply ih
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hStart

end RootBudgetTrace
end StructuralRamsey.RelStructure

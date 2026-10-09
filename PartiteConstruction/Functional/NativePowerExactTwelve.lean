import PartiteConstruction.Functional.NativePowerTwelveBound

/-! # Exact size of the closed functional-power staircase

The existing twelve-cover is surjective onto the closed support.
Its three X-words, three Y-words and six function outputs are also all
distinct. An explicit decoder of the part and two coordinates gives
a left inverse of the twelve-cover. Therefore the support has exactly
twelve vertices, strengthening the previously verified upper bound.

The test is already known to be function-closed and to have no strict
full-function B-tree completion. This is a *source-vertex* count;
the weak projection image is never replaced by a function-generated hull.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

/-- Decode the selected X/Y words and six output words by their roles
and the two old-stage coordinates. Only the twelve-cover needs to obey
the stated input patterns; values away from that image are arbitrary. -/
def staircaseIndex (v : PowerVertex) : Fin 12 :=
  if v.part = 0 then
    if v.coord 0 = 0 then
      if v.coord 1 = 0 then 0 else 1
    else 2
  else if v.part = 1 then
    if v.coord 0 = 2 then
      if v.coord 1 = 2 then 3 else 4
    else 5
  else
    if v.coord 0 = 4 then
      if v.coord 1 = 4 then 6
      else if v.coord 1 = 5 then 7 else 8
    else if v.coord 0 = 5 then
      if v.coord 1 = 5 then 9 else 10
    else 11

/-- The index decoder is a left inverse of the explicit twelve-cover. -/
theorem staircaseIndex_cover (k : Fin 12) :
    staircaseIndex (supportCover k).1 = k := by
  fin_cases k <;> decide

/-- The twelve enumerated vertices are pairwise distinct. -/
theorem supportCover_injective :
    Function.Injective supportCover := by
  intro i j hij
  calc
    i = staircaseIndex (supportCover i).1 :=
      (staircaseIndex_cover i).symm
    _ = staircaseIndex (supportCover j).1 :=
      congrArg (fun z : StaircaseSupport => staircaseIndex z.1) hij
    _ = j := staircaseIndex_cover j

/-- The closed native-power test has exactly twelve vertices. -/
theorem staircaseSupport_card_eq_twelve :
    Nat.card StaircaseSupport = 12 := by
  have hLower : 12 ≤ Nat.card StaircaseSupport := by
    have hcard : Nat.card (Fin 12) ≤ Nat.card StaircaseSupport :=
      Nat.card_le_card_of_injective supportCover supportCover_injective
    simpa using hcard
  exact Nat.le_antisymm staircaseSupport_card_le_twelve hLower

end StructuralRamsey.Structure.NativePowerObstruction

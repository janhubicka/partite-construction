import PartiteConstruction.Functional.NativePowerTreeSquare
import PartiteConstruction.Functional.NativePowerStaircase
import PartiteConstruction.Functional.Induced

/-! # A finite native-function Hales--Jewett power

This records the 3-edge input stage on seven vertices:
  (x0,y0)->z00, (x1,y0)->z10, (x1,y1)->z11.
The actual tagged native `FunctionalPartite.Induced.power` at length two
is used, rather than an unrelated Cartesian-product relation.

The six selected inputs in that power have exactly the staircase
function-domain matrix from `NativePowerStaircase`. The separate
geometric obligations are (i) showing this seven-vertex stage is a full
strict B-tree with an EHN part projection, and (ii) producing its closed
12-vertex full test. -/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

/-- The old part projection, with X=0, Y=1, Z=2. -/
def oldPart (a : Fin 7) : Fin 3 :=
  if a.val < 2 then 0 else if a.val < 4 then 1 else 2

/-- The only three defined binary function inputs of the old stage. -/
def oldOutput (x y : Fin 7) : Option (Fin 7) :=
  if x = 0 ∧ y = 2 then some 4
  else if x = 1 ∧ y = 2 then some 5
  else if x = 1 ∧ y = 3 then some 6
  else none

def oldStage : Structure toyLanguage (Fin 7) where
  rel R xs := oldPart (xs (0 : Fin 1)) = R
  func _ xs := {y |
    oldOutput (xs (0 : Fin 2)) (xs (1 : Fin 2)) = some y}

/-- Each defined input has exactly one output, so transversality is automatic. -/
def oldSystem : FunctionalPartite.System toyLanguage (Fin 3) (Fin 7) where
  toStructure := oldStage
  part := oldPart
  relTransversal := by
    intro R xs hrel i j heq
    have hij : i = j := by
      fin_cases R <;> fin_cases i <;> fin_cases j <;> rfl
    exact congrArg xs hij
  funcTransversal := by
    intro F xs y z hy hz heq
    change oldOutput (xs (0 : Fin 2)) (xs (1 : Fin 2)) = some y at hy
    change oldOutput (xs (0 : Fin 2)) (xs (1 : Fin 2)) = some z at hz
    exact Option.some.inj (hy.symm.trans hz)

/-- A nonempty old fibre always has output in the Z-part. -/
theorem oldOutput_role (x y z : Fin 7)
    (h : oldOutput x y = some z) : oldPart z = 2 := by
  unfold oldOutput at h
  split_ifs at h
  all_goals
    try (cases h; decide)

/-- The three selected words in the X and Y roles. -/
def xWord (i : Fin 3) (k : Fin 2) : Fin 7 :=
  if SelectedWord i k = 0 then 0 else 1

def yWord (j : Fin 3) (k : Fin 2) : Fin 7 :=
  if SelectedWord j k = 0 then 2 else 3

def powerX (i : Fin 3) : FunctionalPartite.Induced.Vertex oldSystem 2 where
  part := 0
  coord := xWord i
  belongs := by
    intro k
    fin_cases i <;> fin_cases k <;> decide

def powerY (j : Fin 3) : FunctionalPartite.Induced.Vertex oldSystem 2 where
  part := 1
  coord := yWord j
  belongs := by
    intro k
    fin_cases j <;> fin_cases k <;> decide

def actualPower :=
  (FunctionalPartite.Induced.power oldSystem 2).toStructure

/-- The input-domain status of a selected pair is exactly the existence
of a value in each of its two coordinates. -/
theorem actualPowerDomain_iff_coordinates (i j : Fin 3) :
    Domain actualPower (powerX i) (powerY j) ↔
      ∀ k : Fin 2,
        ∃ z : Fin 7, oldOutput (xWord i k) (yWord j k) = some z := by
  constructor
  · rintro ⟨z, hz⟩ k
    exact ⟨z.coord k, hz k⟩
  · intro h
    choose z hz using h
    let out : FunctionalPartite.Induced.Vertex oldSystem 2 := {
      part := 2
      coord := z
      belongs := fun k => oldOutput_role
        (xWord i k) (yWord j k) (z k) (hz k)
    }
    exact ⟨out, hz⟩

/-- One old coordinate is defined exactly when its two bit labels form
an allowed input of the three-edge tree. -/
theorem oldCoordinateDomain_iff (i j : Fin 3) (k : Fin 2) :
    (∃ z : Fin 7, oldOutput (xWord i k) (yWord j k) = some z) ↔
      TreeInputDomain (SelectedWord i k) (SelectedWord j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The native tagged power realizes the 100/110/111 staircase exactly. -/
theorem actualPowerDomain_iff_staircase (i j : Fin 3) :
    Domain actualPower (powerX i) (powerY j) ↔ Staircase i j := by
  calc
    Domain actualPower (powerX i) (powerY j) ↔
        ∀ k : Fin 2,
          ∃ z : Fin 7, oldOutput (xWord i k) (yWord j k) = some z :=
      actualPowerDomain_iff_coordinates i j
    _ ↔ SelectedPowerDomain i j := by
      constructor
      · intro h k
        exact (oldCoordinateDomain_iff i j k).mp (h k)
      · intro h k
        exact (oldCoordinateDomain_iff i j k).mpr (h k)
    _ ↔ Staircase i j := selectedPowerDomain_iff_staircase i j

/-- In any square-free target, no full function-fibre-exact image of
these six actual native-power inputs exists. -/
theorem actualPower_noSquareTarget
    {X Y : Type} (R : X → Y → Prop)
    (hNoSquare : NoSquare R)
    (fx : Fin 3 → X) (fy : Fin 3 → Y)
    (hExact : ∀ i j,
       R (fx i) (fy j) ↔
       Domain actualPower (powerX i) (powerY j)) : False := by
  exact staircase_noSquare_obstruction R hNoSquare fx fy
    (fun i j => (hExact i j).trans (actualPowerDomain_iff_staircase i j))

end StructuralRamsey.Structure.NativePowerObstruction

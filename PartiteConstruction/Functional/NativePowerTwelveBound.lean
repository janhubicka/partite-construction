import PartiteConstruction.Functional.NativePowerClosedStaircase

/-! # A twelve-vertex budget for the closed native-power staircase

The chosen closed staircase support consists of three X-words, three Y-words
and six Z-words. We do not assume any computable enumeration of the whole
dependent tagged-power carrier.

Instead an explicit map from Fin 12 onto the support provides the cardinal
bound. This is the bound relevant to the local tree-completion induction:
at most twelve *actual* source vertices, never their generated closure.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The six coordinate pairs supplied by the six defined staircase fibres. -/
def zWord (k : Fin 6) : Fin 2 → Fin 7 :=
  if k = 0 then ![4,4]
  else if k = 1 then ![4,5]
  else if k = 2 then ![4,6]
  else if k = 3 then ![5,5]
  else if k = 4 then ![5,6]
  else ![6,6]

def powerZ (k : Fin 6) : PowerVertex where
  part := 2
  coord := zWord k
  belongs := by
    intro i
    fin_cases k <;> fin_cases i <;> decide

def zSourceX (k : Fin 6) : Fin 3 :=
  if k = 0 then 0 else if k = 1 ∨ k = 2 then 1 else 2

def zSourceY (k : Fin 6) : Fin 3 :=
  if k = 0 ∨ k = 1 ∨ k = 3 then 0
  else if k = 2 ∨ k = 4 then 1 else 2

/-- Every explicitly indexed Z-word is an actual output of its
corresponding selected pair. -/
theorem powerZ_is_output (k : Fin 6) :
    powerZ k ∈ actualPower.func ()
      ![powerX (zSourceX k),powerY (zSourceY k)] := by
  intro i
  change oldOutput (xWord (zSourceX k) i)
      (yWord (zSourceY k) i) = some (zWord k i)
  fin_cases k <;> fin_cases i <;> decide

theorem powerZ_mem_support (k : Fin 6) :
    powerZ k ∈ StaircaseSupport :=
  Or.inr (Or.inr ⟨zSourceX k,zSourceY k,powerZ_is_output k⟩)

/-- Every defined pair of selected X/Y-words has its output represented by
one of the six explicit Z-words. This is a closed, finite calculation. -/
theorem zWord_covers_definedPairs :
    ∀ i j : Fin 3, Staircase i j →
      ∃ k : Fin 6,
        ∀ t : Fin 2,
          oldOutput (xWord i t) (yWord j t) = some (zWord k t) := by
  decide

/-- Every output over a selected pair belongs to the six-element
Z-family. Function-output transversality gives uniqueness inside each
target part, so no arbitrary choices or closure hulls are needed. -/
theorem selectedOutput_in_powerZ_range
    (i j : Fin 3) (z : PowerVertex)
    (hz : z ∈ actualPower.func () ![powerX i,powerY j]) :
    ∃ k : Fin 6, z = powerZ k := by
  have hDom : Staircase i j :=
    (actualPowerDomain_iff_staircase i j).mp ⟨z,hz⟩
  obtain ⟨k,hk⟩ := zWord_covers_definedPairs i j hDom
  have hCandidate :
      powerZ k ∈ actualPower.func () ![powerX i,powerY j] := hk
  have hSamePart : z.part = (powerZ k).part :=
    (actualPower_output_roles _ _ _ hz).2.2
  have heq := (FunctionalPartite.Induced.power oldSystem 2).funcTransversal
    () ![powerX i,powerY j] z (powerZ k) hz hCandidate hSamePart
  exact ⟨k,heq⟩

/-- The twelve-index covering map: first three selected X inputs,
next three Y inputs, final six actual function outputs. -/
def supportCoverVertex (k : Fin 12) : PowerVertex :=
  if h : k.val < 3 then powerX ⟨k.val,h⟩
  else if h : k.val < 6 then powerY ⟨k.val - 3,by omega⟩
  else powerZ ⟨k.val - 6,by omega⟩

theorem supportCoverVertex_mem (k : Fin 12) :
    supportCoverVertex k ∈ StaircaseSupport := by
  unfold supportCoverVertex
  split_ifs with h h'
  · exact powerX_mem_support _
  · exact powerY_mem_support _
  · exact powerZ_mem_support _

def supportCover (k : Fin 12) : StaircaseSupport :=
  ⟨supportCoverVertex k,supportCoverVertex_mem k⟩

/-- No vertex of the closed support lies outside the twelve-index cover. -/
theorem supportCover_surjective :
    Function.Surjective supportCover := by
  intro v
  rcases v.2 with hX | hY | hZ
  · obtain ⟨i,hi⟩ := hX
    refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Subtype.ext
    fin_cases i <;> exact hi.symm
  · obtain ⟨j,hj⟩ := hY
    refine ⟨⟨j.val + 3,by omega⟩,?_⟩
    apply Subtype.ext
    fin_cases j <;> exact hj.symm
  · obtain ⟨i,j,hz⟩ := hZ
    obtain ⟨k,hk⟩ := selectedOutput_in_powerZ_range i j v.1 hz
    refine ⟨⟨k.val + 6,by omega⟩,?_⟩
    apply Subtype.ext
    fin_cases k <;> exact hk.symm

/-- A bounded cardinality certificate for the genuine closed test.
Only the twelve chosen source vertices are charged to the rank. -/
theorem staircaseSupport_card_le_twelve :
    Nat.card StaircaseSupport ≤ 12 := by
  classical
  let pick : StaircaseSupport → Fin 12 :=
    fun v => Classical.choose (supportCover_surjective v)
  have hpick (v : StaircaseSupport) : supportCover (pick v) = v :=
    Classical.choose_spec (supportCover_surjective v)
  have hinj : Function.Injective pick := by
    intro a b hab
    calc
      a = supportCover (pick a) := (hpick a).symm
      _ = supportCover (pick b) := congrArg supportCover hab
      _ = b := hpick b
  letI : Finite StaircaseSupport := Finite.of_injective pick hinj
  have hcard : Nat.card StaircaseSupport ≤ Nat.card (Fin 12) :=
    Nat.card_le_card_of_injective pick hinj
  simpa using hcard

end StructuralRamsey.Structure.NativePowerObstruction

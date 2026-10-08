import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-! # The finite staircase obstruction to domain-square-free targets

The selected six input vertices in the candidate EHN power test have
binary-function domain matrix

  1 0 0
  1 1 0
  1 1 1

Any mapping preserving AND reflecting *whether each binary-function
fibre is nonempty* to a square-free bipartite domain graph is impossible.
The two extra vertices outside the K2,2 force its four vertices to
remain distinct. This is the finite combinatorial half of the
power-obstruction argument; the separate tree-theoretic obligation is to
show that the full B-tree targets have square-free domain graphs.

This file makes **no** claim about all native EHN stages or about the
final n-pass statement. -/

namespace StructuralRamsey.Structure.NativePowerObstruction

universe u v

/-- The exact binary-function domain matrix on the three selected X-parts
and the three selected Y-parts. -/
def Staircase (i j : Fin 3) : Prop := j.val ≤ i.val

instance staircaseDecidable (i j : Fin 3) : Decidable (Staircase i j) :=
  inferInstanceAs (Decidable (j.val ≤ i.val))

/-- No induced/undirected 4-cycle among the two distinguished input roles.
For the template with one binary-function hyperedge, this condition is
satisfied by any full strict B-tree (the independent tree induction is
not part of this lemma). -/
def NoSquare {X Y : Type v} (R : X → Y → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂, x₁ ≠ x₂ → y₁ ≠ y₂ →
    R x₁ y₁ → R x₁ y₂ → R x₂ y₁ → R x₂ y₂ → False

/-- The staircase matrix cannot be realized under a domain-exact map into
a square-free target. In particular, a full function homomorphism with
complete image fibres cannot collapse its displayed K2,2. -/
theorem staircase_noSquare_obstruction
    {X Y : Type v} (R : X → Y → Prop)
    (hNoSquare : NoSquare R)
    (fx : Fin 3 → X) (fy : Fin 3 → Y)
    (hExact : ∀ i j : Fin 3,
      R (fx i) (fy j) ↔ Staircase i j) :
    False := by
  have hx : fx 1 ≠ fx 2 := by
    intro heq
    have h22 : R (fx 2) (fy 2) :=
      (hExact 2 2).2 (by decide)
    have h12 : R (fx 1) (fy 2) := by
      rw [heq]
      exact h22
    have hbad : Staircase 1 2 := (hExact 1 2).1 h12
    exact (by decide : ¬ Staircase (1 : Fin 3) (2 : Fin 3)) hbad
  have hy : fy 0 ≠ fy 1 := by
    intro heq
    have h00 : R (fx 0) (fy 0) :=
      (hExact 0 0).2 (by decide)
    have h01 : R (fx 0) (fy 1) := by
      rw [← heq]
      exact h00
    have hbad : Staircase 0 1 := (hExact 0 1).1 h01
    exact (by decide : ¬ Staircase (0 : Fin 3) (1 : Fin 3)) hbad
  have e10 : R (fx 1) (fy 0) := (hExact 1 0).2 (by decide)
  have e11 : R (fx 1) (fy 1) := (hExact 1 1).2 (by decide)
  have e20 : R (fx 2) (fy 0) := (hExact 2 0).2 (by decide)
  have e21 : R (fx 2) (fy 1) := (hExact 2 1).2 (by decide)
  exact hNoSquare (fx 1) (fx 2) (fy 0) (fy 1)
    hx hy e10 e11 e20 e21

/-- The binary-function domain of the three-edge tree: all pairs except
(x0,y1) are defined. This is a concrete relation on its X- and Y-parts. -/
def TreeInputDomain (i j : Fin 2) : Prop :=
  i = 1 ∨ j = 0

instance treeInputDomainDecidable (i j : Fin 2) : Decidable (TreeInputDomain i j) :=
  inferInstanceAs (Decidable (i = 1 ∨ j = 0))

/-- The three selected words 00, 01, 11 in each part of the second
coordinatewise Hales--Jewett power. -/
def SelectedWord (i : Fin 3) (k : Fin 2) : Fin 2 :=
  if i = 0 then 0 else if i = 1 then if k = 0 then 0 else 1 else 1

/-- A binary-function input is defined in the tagged coordinatewise power
exactly when it is defined in both old coordinates. -/
def SelectedPowerDomain (i j : Fin 3) : Prop :=
  ∀ k : Fin 2, TreeInputDomain (SelectedWord i k) (SelectedWord j k)

instance selectedPowerDomainDecidable (i j : Fin 3) : Decidable (SelectedPowerDomain i j) :=
  inferInstanceAs (Decidable (∀ k : Fin 2, TreeInputDomain (SelectedWord i k) (SelectedWord j k)))

/-- The computed second-power domain matrix is the staircase 100/110/111.
Unlike a generated function closure, the tested image here has exactly
the selected vertices. -/
theorem selectedPowerDomain_iff_staircase
    (i j : Fin 3) :
    SelectedPowerDomain i j ↔ Staircase i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The concrete domain matrix of these six power inputs already prohibits
a full domain-exact map to any square-free target. -/
theorem selectedPowerDomain_noSquare
    {X Y : Type v} (R : X → Y → Prop)
    (hNoSquare : NoSquare R)
    (fx : Fin 3 → X) (fy : Fin 3 → Y)
    (hExact : ∀ i j : Fin 3,
      R (fx i) (fy j) ↔ SelectedPowerDomain i j) :
    False := by
  apply staircase_noSquare_obstruction R hNoSquare fx fy
  intro i j
  exact (hExact i j).trans (selectedPowerDomain_iff_staircase i j)

end StructuralRamsey.Structure.NativePowerObstruction

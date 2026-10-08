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

end StructuralRamsey.Structure.NativePowerObstruction

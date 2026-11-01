import PartiteConstruction.HalesJewett.Finite

/-!
# Track D: seven-cycle in the exact three-line Hales--Jewett graph skeleton

This is a finite, kernel-checked counterpart of
`checks/native_hj_line_only_seven_cycle.py`.
There are two full old A-letters, a and b, on two part fibres
0 and 1, with a bridge vertex c adjacent to a0 and b1.
The genuine tagged Hales--Jewett power of the selected two disjoint
A-edges is a matching: at each binary word one part-0 and one
part-1 core vertex are adjacent. A FULL old copy attached along
a line W contributes a fresh exterior vertex c_W, joined to the
exact images W(a0) and W(b1).

At length two take the THREE ACTUAL line symbol maps
  W0=(b,p), W1=(p,a), W2=(p,p).
The seven explicitly listed vertices form an induced C7, and no
two-colouring of the complete finite graph skeleton is possible.
This is an adversarial regression of the LINE-ONLY history geometry,
not an independent construction of the actual native EHN Stage or
a refutation of the corrected 2019 class Ramsey theorem. The next
step is to transport this finite skeleton into the genuine
FunctionalPartite.EHN.attachList stage, with full maps and class
hypotheses checked separately.
-/

namespace StructuralRamsey.Structure.TrackD.HJLineC7

open StructuralRamsey.HalesJewett
open SuccessorTree

/-- Letter a = false, letter b = true; p is the varying parameter. -/
def W0 : Line Bool 2 where
  symbol i := if i = 0 then .const true else .parameter
  hasParameter := ⟨1, by decide⟩

def W1 : Line Bool 2 where
  symbol i := if i = 0 then .parameter else .const false
  hasParameter := ⟨0, by decide⟩

def W2 : Line Bool 2 where
  symbol _ := .parameter
  hasParameter := ⟨0, rfl⟩

def line : Fin 3 → Line Bool 2
  | 0 => W0
  | 1 => W1
  | _ => W2

/-- True HJ coordinatewise selected-support word (two old A-letters).
One core vertex is the word and its part tag. -/
abbrev Word := Fin 2 → Bool

/-- Full core plus exactly THREE fresh exterior OLD-copy vertices.
There are no phantom edges or extra copies in this finite skeleton. -/
inductive Vertex where
  | core : Bool → Word → Vertex
  | outside : Fin 3 → Vertex
  deriving DecidableEq

/-- Edges in the ACTUAL coordinatewise power plus the two exterior
edges contributed by each old P5 copy along its exact full HJ line.
The selected substructure is the two disjoint A-edges; in particular
the old exterior c is linked to the a0 and b1 boundary vertices. -/
def Edge : Vertex → Vertex → Prop
  | .core p u, .core q v => p ≠ q ∧ u = v
  | .outside w, .core p u =>
      (p = false ∧ u = (line w).eval false) ∨
      (p = true  ∧ u = (line w).eval true)
  | .core p u, .outside w =>
      (p = false ∧ u = (line w).eval false) ∨
      (p = true  ∧ u = (line w).eval true)
  | .outside _, .outside _ => False

/-- This is the seven-cycle
  c0, (b0,a0), (b1,a1), c1, (a0,a0), c2, (b1,b1), c0.
The four core vertices are the exact tagged power words, not an
unrelated Cartesian-product edge system. -/
def cycle : Fin 7 → Vertex
  | 0 => .outside 0
  | 1 => .core false (W0.eval false)
  | 2 => .core true  (W1.eval true)
  | 3 => .outside 1
  | 4 => .core false (W1.eval false)
  | 5 => .outside 2
  | _ => .core true  (W2.eval true)

def next (i : Fin 7) : Fin 7 :=
  ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩

/-- All seven cycle vertices are distinct. -/
theorem cycle_injective : Function.Injective cycle := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cycle, W0, W1, W2, Line.eval, LineSymbol.eval]

/-- The graph contains the seven exact cyclic edges. -/
theorem cycle_edge (i : Fin 7) :
    Edge (cycle i) (cycle (next i)) := by
  fin_cases i <;> decide

/-- There are no chords: the seven-vertex induced graph is EXACTLY
the C7 edge set. In particular the core matching edge is genuine
and each outside OLD-copy vertex has exactly its prescribed
two attaching edges. -/
theorem cycle_induced_iff (i j : Fin 7) :
    Edge (cycle i) (cycle j) ↔ next i = j ∨ next j = i := by
  fin_cases i <;> fin_cases j <;> decide

/-- W0 and W1 have disjoint parameter sets, while W2 is fully
parametric. No single coordinate evaluates all three full OLD
support line embeddings as the identity. -/
theorem no_common_parameter :
    ¬ ∃ i : Fin 2,
      W0.symbol i = .parameter ∧
      W1.symbol i = .parameter ∧
      W2.symbol i = .parameter := by
  decide

/-- An odd cycle in the actual three-line skeleton prevents any
graph homomorphism to a bipartite strict K2-tree. This proves a
genuine THREE-line compatibility obstruction at the finite
coordinate-history level; it does not falsely declare the old
Ramsey control K3 to be Ramsey for unordered K2 embeddings. -/
theorem not_twoColorable :
    ¬ ∃ c : Vertex → Bool,
      ∀ x y : Vertex, Edge x y → c x ≠ c y := by
  rintro ⟨c, hc⟩
  have propagates (x y z : Vertex)
      (hxy : c x ≠ c y) (hyz : c y ≠ c z) :
      c x = c z := by
    cases hx : c x <;> cases hy : c y <;>
      cases hz : c z <;> simp_all
  have h01 : c (cycle 0) ≠ c (cycle 1) :=
    hc _ _ (by decide)
  have h12 : c (cycle 1) ≠ c (cycle 2) :=
    hc _ _ (by decide)
  have h23 : c (cycle 2) ≠ c (cycle 3) :=
    hc _ _ (by decide)
  have h34 : c (cycle 3) ≠ c (cycle 4) :=
    hc _ _ (by decide)
  have h45 : c (cycle 4) ≠ c (cycle 5) :=
    hc _ _ (by decide)
  have h56 : c (cycle 5) ≠ c (cycle 6) :=
    hc _ _ (by decide)
  have h60 : c (cycle 6) ≠ c (cycle 0) :=
    hc _ _ (by decide)
  have h02 : c (cycle 0) = c (cycle 2) :=
    propagates _ _ _ h01 h12
  have h24 : c (cycle 2) = c (cycle 4) :=
    propagates _ _ _ h23 h34
  have h46 : c (cycle 4) = c (cycle 6) :=
    propagates _ _ _ h45 h56
  exact h60 (h02.trans (h24.trans h46)).symm

end StructuralRamsey.Structure.TrackD.HJLineC7

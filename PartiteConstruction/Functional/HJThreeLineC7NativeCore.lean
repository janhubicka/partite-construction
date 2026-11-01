import PartiteConstruction.Functional.MaximalHardRootFiveCycleFixture
import PartiteConstruction.Functional.WeakInduced

/-!
# Track D: REAL native functional two-letter HJ power for the C7 audit

The C7 graph skeleton uses two selected full K2 letters (a,b) and
the true HJ line words (b,p), (p,a), (p,p). This module puts that
selected support INSIDE the actual FunctionalPartite.System and
FunctionalPartite.Induced.power APIs rather than treating the
coordinatewise core as an unrelated matching graph.

The native language is function-free here, but the construction is
the very same full-functional induced power used for genuine
set-valued function systems. The native two-vertex A is an edge,
the four-vertex selected support is a disjoint union of TWO edges,
its part map is the first Boolean coordinate, and the two constants
are FULL functional-partite embeddings of A into the selected support.

The real power has four core words in each part, and the displayed
W0/W1/W2 line maps satisfy the precise coordinate equations of the
C7 construction. The matching cross-edge is a true relation tuple
in the actual native power. This module DOES NOT assemble the three
full old P5 attachments, prove the final C7 closed test inside
that Stage, or derive a strict B-tree refutation for a source with
the predecessor-rank assumptions.
-/

namespace StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.HalesJewett
open SuccessorTree

abbrev Lang := StructuralRamsey.Structure.MaximalHardRootFiveCycle.language

/-- A single graph edge on two parts; no function symbols. -/
def A : Structure Lang Bool where
  rel Rel xs := by
    cases Rel
    change (Fin 2 → Bool) at xs
    exact xs 0 ≠ xs 1
  func F := Empty.elim F

/-- The actual four-vertex selected support of an old P5 stage:
two disjoint A-edges, with first coordinate the part and second
coordinate the letter a/b. -/
def R : FunctionalPartite.System Lang Bool (Bool × Bool) where
  toStructure := {
    rel Rel xs := by
      cases Rel
      change (Fin 2 → Bool × Bool) at xs
      exact (xs 0).1 ≠ (xs 1).1 ∧ (xs 0).2 = (xs 1).2
    func F := Empty.elim F
  }
  part := Prod.fst
  relTransversal := by
    intro Rel xs h i j hij
    cases Rel
    change (Fin 2 → Bool × Bool) at xs
    change (xs 0).1 ≠ (xs 1).1 ∧
      (xs 0).2 = (xs 1).2 at h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h.1 hij).elim
    · exact (h.1 hij.symm).elim
    · rfl
  funcTransversal := by
    intro F
    exact Empty.elim F

/-- Projection from the disjoint union of two full A-copies is
a weak EHN homomorphism. It is NOT a full graph homomorphism: the
two copies have no cross edges. -/
theorem R_weakProjection :
    R.toStructure.IsWeakHomomorphism A R.part := by
  constructor
  · intro Rel xs h
    cases Rel
    change (Fin 2 → Bool × Bool) at xs
    change (xs 0).1 ≠ (xs 1).1 ∧
      (xs 0).2 = (xs 1).2 at h
    exact h.1
  · intro F
    exact Empty.elim F

/-- Both full A letters in the genuine selected support. -/
def letter (a : Bool) :
    FunctionalPartite.Embedding (transversal A) R where
  toEmbedding := {
    toFun := fun p => (p, a)
    injective := by
      intro x y h
      exact congrArg Prod.fst h
    map_rel_iff := by
      intro Rel xs
      cases Rel
      change (Fin 2 → Bool) at xs
      change (xs 0 ≠ xs 1 ∧ a = a) ↔ xs 0 ≠ xs 1
      simp
    map_func := by
      intro F
      exact Empty.elim F
  }
  map_part := fun _ => rfl

/-- Three actual Hales--Jewett lines of the FULL two-letter alphabet. -/
def W0 : Line (Induced.Letter A R) 2 where
  symbol i := if i = 0 then .const (letter true) else .parameter
  hasParameter := ⟨1, rfl⟩

def W1 : Line (Induced.Letter A R) 2 where
  symbol i := if i = 0 then .parameter else .const (letter false)
  hasParameter := ⟨0, rfl⟩

def W2 : Line (Induced.Letter A R) 2 where
  symbol _ := .parameter
  hasParameter := ⟨0, rfl⟩

/-- Explicit tagged coordinatewise-power vertex, with separate
part and Boolean word coordinates as in the combinatorial C7
regression. -/
def coreVertex (p : Bool) (a b : Bool) : Induced.Vertex R 2 where
  part := p
  coord i := (p, if i = 0 then a else b)
  belongs _ := rfl

/-- Exact full line W0(a0)=(b0,a0) in the REAL HJ power. -/
theorem W0_a0 :
    Induced.lineMap W0 (false, false) =
      coreVertex false true false := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W0 (false, false))
    (y := coreVertex false true false) rfl
  intro i
  fin_cases i <;> rfl

/-- Exact full line W1(b1)=(b1,a1) in the REAL HJ power. -/
theorem W1_b1 :
    Induced.lineMap W1 (true, true) =
      coreVertex true true false := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W1 (true, true))
    (y := coreVertex true true false) rfl
  intro i
  fin_cases i <;> rfl

theorem W1_a0 :
    Induced.lineMap W1 (false, false) =
      coreVertex false false false := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W1 (false, false))
    (y := coreVertex false false false) rfl
  intro i
  fin_cases i <;> rfl

theorem W2_a0 :
    Induced.lineMap W2 (false, false) =
      coreVertex false false false := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W2 (false, false))
    (y := coreVertex false false false) rfl
  intro i
  fin_cases i <;> rfl

theorem W2_b1 :
    Induced.lineMap W2 (true, true) =
      coreVertex true true true := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W2 (true, true))
    (y := coreVertex true true true) rfl
  intro i
  fin_cases i <;> rfl

theorem W0_b1 :
    Induced.lineMap W0 (true, true) =
      coreVertex true true true := by
  apply Induced.Vertex.ext (B := R)
    (x := Induced.lineMap W0 (true, true))
    (y := coreVertex true true true) rfl
  intro i
  fin_cases i <;> rfl

/-- The single cross-edge between W0(a0) and W1(b1) is an
ACTUAL relation tuple of the native power, not a graph-edge
postulated in a free combinatorial skeleton. -/
theorem native_core_cross_edge :
    (Induced.power R 2).rel () (fun k : Fin 2 =>
      if k = 0 then Induced.lineMap W0 (false, false)
        else Induced.lineMap W1 (true, true)) := by
  rw [W0_a0, W1_b1]
  intro i
  fin_cases i
  · change (false ≠ true ∧ true = true)
    decide
  · change (false ≠ true ∧ false = false)
    decide

/-- Both selected A copies embed FULLY, and consequently all three
HJ lines are genuine full functional partite embeddings into the
native power. The projection is only source-defined weak. -/
theorem full_native_lines :
    ∀ W : Line (Induced.Letter A R) 2,
      Nonempty (FunctionalPartite.Embedding R (Induced.power R 2)) := by
  intro W
  exact ⟨Induced.weak_lineEmbedding R_weakProjection W⟩

end StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

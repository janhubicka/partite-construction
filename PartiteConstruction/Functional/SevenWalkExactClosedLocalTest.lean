import PartiteConstruction.Functional.HJThreeLineC7NativeCore
import PartiteConstruction.Structure.WeakHomomorphism

/-!
# Track D: exact seven-vertex closed-test extraction from a genuine graph odd walk

A family of full function-language attachments may carry a seven-edge
odd closed walk, even when it has many more ambient vertices. The original
functional iteration needs tests on EXACT finite vertex sets, not
generated closure hulls. For the graph-only language used by the actual
native Hales--Jewett C7 fixture, every subset is function-closed.

This module supplies an independent reusable endpoint: a seven-edge
walk in ANY structure in that language produces one literal closed
test of size <= 7 whose full induced structure cannot be two-coloured
and admits no EHN/weak projection into any bipartite target.
No injectivity or distinctness premise is needed for the parity
contradiction. We do not assume a relation-only surrogate; the
test is a genuine induced full functional Structure.

The existence of a seven-edge walk in a specific SEQUENTIAL native
HJ Picture is a separate issue, handled in Track D's sequential
three-line construction. This file is the general exact-rank endpoint.
-/

namespace StructuralRamsey.Structure.TrackD.SevenWalkLocality

open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

variable {X : Type}

/-- Successor in the literal cyclic order on seven indices. -/
def next (i : Fin 7) : Fin 7 :=
  ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩

/-- Exactly seven listed ambient vertices, possibly with collisions.
No closure hull or extra vertices enter the local test. -/
noncomputable def test (v : Fin 7 → X) : Finset X := by
  classical
  exact (Finset.univ : Finset (Fin 7)).image v

theorem test_card_le_seven (v : Fin 7 → X) :
    (test v).card ≤ 7 := by
  classical
  simpa [test] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := v))

/-- Every literal vertex set is function-closed for the graph-only
native language. In particular, the exact cycle test is closed. -/
theorem test_closed (A : Structure Lang X) (v : Fin 7 → X) :
    A.IsClosed (↑(test v) : Set X) := by
  intro F
  exact Empty.elim F

/-- The exact induced full-functional source test. -/
noncomputable def small (A : Structure Lang X) (v : Fin 7 → X) :
    Structure Lang (↑(test v) : Set X) :=
  A.induce (↑(test v) : Set X) (test_closed A v)

/-- Each listed odd-walk vertex lies inside the exact same local test. -/
noncomputable def localVertex (v : Fin 7 → X) (i : Fin 7) :
    (↑(test v) : Set X) := by
  classical
  exact ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- Seven actual source edges remain seven actual edges in the SAME
full-function induced local test, with no increase of cardinality. -/
theorem local_edge
    (A : Structure Lang X) (v : Fin 7 → X)
    (hEdges : ∀ i : Fin 7,
      A.rel () (fun k : Fin 2 =>
        if k = 0 then v i else v (next i)))
    (i : Fin 7) :
    (small A v).rel () (fun k : Fin 2 =>
      if k = 0 then localVertex v i else localVertex v (next i)) := by
  change A.rel () (Subtype.val ∘
    (fun k : Fin 2 => if k = 0 then localVertex v i else localVertex v (next i)))
  have hTuple :
      (Subtype.val ∘ (fun k : Fin 2 =>
        if k = 0 then localVertex v i else localVertex v (next i))) =
      (fun k : Fin 2 => if k = 0 then v i else v (next i)) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk, Function.comp_apply, localVertex]
  exact Eq.mp
    (congrArg (fun xs : Fin 2 → X => A.rel () xs) hTuple.symm)
    (hEdges i)

/-- Any seven-edge odd closed walk contradicts two-colourability
already on the EXACT induced local test, even when its seven
vertex names were not proved distinct. -/
theorem small_not_twoColorable
    (A : Structure Lang X) (v : Fin 7 → X)
    (hEdges : ∀ i : Fin 7,
      A.rel () (fun k : Fin 2 =>
        if k = 0 then v i else v (next i))) :
    ¬ ∃ c : (↑(test v) : Set X) → Bool,
      ∀ x y : (↑(test v) : Set X),
        (small A v).rel () (fun k : Fin 2 =>
          if k = 0 then x else y) → c x ≠ c y := by
  rintro ⟨c, hc⟩
  have hEdge (i : Fin 7) :
      c (localVertex v i) ≠ c (localVertex v (next i)) :=
    hc _ _ (local_edge A v hEdges i)
  have h01 : c (localVertex v 0) ≠ c (localVertex v 1) := by
    simpa [next] using hEdge 0
  have h12 : c (localVertex v 1) ≠ c (localVertex v 2) := by
    simpa [next] using hEdge 1
  have h23 : c (localVertex v 2) ≠ c (localVertex v 3) := by
    simpa [next] using hEdge 2
  have h34 : c (localVertex v 3) ≠ c (localVertex v 4) := by
    simpa [next] using hEdge 3
  have h45 : c (localVertex v 4) ≠ c (localVertex v 5) := by
    simpa [next] using hEdge 4
  have h56 : c (localVertex v 5) ≠ c (localVertex v 6) := by
    simpa [next] using hEdge 5
  have h60 : c (localVertex v 6) ≠ c (localVertex v 0) := by
    simpa [next] using hEdge 6
  have eq_of_ne_ne {a b d : Bool} (hab : a ≠ b) (hbd : b ≠ d) :
      a = d := by
    cases a <;> cases b <;> cases d <;> simp_all
  have h02 : c (localVertex v 0) = c (localVertex v 2) :=
    eq_of_ne_ne h01 h12
  have h24 : c (localVertex v 2) = c (localVertex v 4) :=
    eq_of_ne_ne h23 h34
  have h46 : c (localVertex v 4) = c (localVertex v 6) :=
    eq_of_ne_ne h45 h56
  exact h60 (h02.trans (h24.trans h46)).symm

/-- An exact seven-vertex closed weak test with an odd walk has NO
source-defined weak homomorphism to ANY bipartite graph target.
This is a source-function-language theorem, not a fake total-fibre
projection and not a claim about the ancestor control's rank. -/
theorem small_no_weak_hom_to_bipartite
    {Y : Type} (A : Structure Lang X) (v : Fin 7 → X)
    (hEdges : ∀ i : Fin 7,
      A.rel () (fun k : Fin 2 =>
        if k = 0 then v i else v (next i)))
    (B : Structure Lang Y)
    (hBip : ∃ c : Y → Bool,
      ∀ a b : Y,
        B.rel () (fun k : Fin 2 =>
          if k = 0 then a else b) → c a ≠ c b) :
    ¬ ∃ f : (↑(test v) : Set X) → Y,
      (small A v).IsWeakHomomorphism B f := by
  rintro ⟨f, hf⟩
  obtain ⟨c, hc⟩ := hBip
  apply small_not_twoColorable A v hEdges
  refine ⟨c ∘ f, ?_⟩
  intro x y hxy
  have hMap := hf.1 ()
    (fun k : Fin 2 => if k = 0 then x else y) hxy
  have hTarget : B.rel () (fun k : Fin 2 =>
      if k = 0 then f x else f y) := by
    have hTuple :
        (f ∘ (fun k : Fin 2 => if k = 0 then x else y)) =
        (fun k : Fin 2 => if k = 0 then f x else f y) := by
      funext k
      by_cases hk : k = 0 <;> simp [hk, Function.comp_apply]
    rw [← hTuple]
    exact hMap
  exact hc (f x) (f y) hTarget

end StructuralRamsey.Structure.TrackD.SevenWalkLocality

import PartiteConstruction.Functional.HJThreeLineNativeFullAttachmentC7

/-!
# Track D: exact seven-vertex CLOSED mixed test inside the native HJ attachment

The odd C7 obstruction is not merely a property of the complete
(possibly much larger) three-copy functional source. Its seven
explicit native vertices form an exact finite subset of size <=7.
Since the language has NO function symbols, that exact subset
is function-closed without inserting a single closure vertex.

The induced full functional structure on this exact test has no
two-colouring, witnessed by the same seven literal native relation
tuples. Therefore this is a genuine small-test obstruction to
UNRESTRICTED strict K2-tree locality in a naive native multi-line
attachment. It still does not contradict the rank successor:
the control contains a triangle, hence its strict predecessor
locality at rank >=3 already fails.

No general `TreeAmalgam` endpoint is claimed until a checked
strict-K2-tree-to-two-colouring bridge has been applied to this
same exact test and the necessary Stage assumptions are audited.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey.Structure

/-- The EXACT seven native cycle vertices, with no generated hull. -/
noncomputable def exactCycle : Finset Vertex :=
  (Finset.univ : Finset (Fin 7)).image cycle

theorem exactCycle_card_le_seven : exactCycle.card ≤ 7 := by
  classical
  have h := Finset.card_image_le
    (s := (Finset.univ : Finset (Fin 7))) (f := cycle)
  simpa only [exactCycle, Finset.card_univ, Fintype.card_fin] using h

/-- The actual tested subset is function-closed, vacuously because
the original graph language has no function symbols. -/
theorem exactCycle_closed :
    Whole.toStructure.IsClosed (↑exactCycle : Set Vertex) := by
  intro F
  exact Empty.elim F

/-- Exact closed full-functional induced seven-vertex test.
The source carrier is the literal selected subset. -/
noncomputable abbrev Small :=
  Whole.toStructure.induce
    (↑exactCycle : Set Vertex) exactCycle_closed

private def next (i : Fin 7) : Fin 7 :=
  ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩

/-- The actual seven native vertices viewed as vertices of
the SAME exact induced functional test. -/
noncomputable def smallCycle (i : Fin 7) :
    (↑exactCycle : Set Vertex) :=
  ⟨cycle i, by
    classical
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem smallCycle_edge (i : Fin 7) :
    Small.rel () (fun k : Fin 2 =>
      if k = 0 then smallCycle i else smallCycle (next i)) := by
  change Whole.toStructure.rel () (fun k : Fin 2 =>
    if k = 0 then cycle i else cycle (next i))
  exact cycle_edge i

/-- No proper two-colouring of the TRUE exact induced local test
exists. This is strictly stronger than a failure to colour
the full ambient attachment. -/
theorem exactCycle_not_twoColorable :
    ¬ ∃ c : (↑exactCycle : Set Vertex) → Bool,
      ∀ x y : (↑exactCycle : Set Vertex),
        Small.rel () (fun k : Fin 2 =>
          if k = 0 then x else y) →
        c x ≠ c y := by
  rintro ⟨c, hc⟩
  have eq_of_ne_ne {x y z : Bool}
      (hxy : x ≠ y) (hyz : y ≠ z) : x = z := by
    cases x <;> cases y <;> cases z <;> simp_all
  have hEdge (i : Fin 7) :
      c (smallCycle i) ≠ c (smallCycle (next i)) :=
    hc _ _ (smallCycle_edge i)
  have h01 := hEdge 0
  have h12 := hEdge 1
  have h23 := hEdge 2
  have h34 := hEdge 3
  have h45 := hEdge 4
  have h56 := hEdge 5
  have h60 := hEdge 6
  have h02 : c (smallCycle 0) = c (smallCycle 2) :=
    eq_of_ne_ne h01 h12
  have h24 : c (smallCycle 2) = c (smallCycle 4) :=
    eq_of_ne_ne h23 h34
  have h46 : c (smallCycle 4) = c (smallCycle 6) :=
    eq_of_ne_ne h45 h56
  exact h60 (h02.trans (h24.trans h46)).symm

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7

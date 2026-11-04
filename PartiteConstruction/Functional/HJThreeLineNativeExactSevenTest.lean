import PartiteConstruction.Functional.SevenWalkExactClosedLocalTest
import PartiteConstruction.Functional.HJThreeLineNativeFullAttachmentC7

/-!
# Track D: the ACTUAL native full attachment has an exact closed rank-seven C7 test

This combines two already checked independent ingredients:
(1) the real Fin-3 indexed full-functional three-copy Hales--Jewett
attachment contains seven consecutive graph edges, and
(2) a finite odd closed walk in a function-free signature gives an
EXACT closed vertex test with the same bound and no weak homomorphism
to any bipartite target.

The test is literally the image of the seven named native cycle
vertices, not a closure hull. It is a full `Structure.induce` in
the original functional language, with NO additional vertices or
premature U-closure. Its weak-map obstruction holds for the ORIGINAL
P5 target.

This checks the bounded-test strengthening missing from the earlier
PR #545. The result is an obstruction to naive strict-tree locality
for an arbitrary HJ line history, not to the rank-successor lemma:
the triangle forced by the P5 part projection already invalidates
the predecessor locality at rank at least three.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackD.SevenWalkLocality

/-- Exactly the seven displayed vertices of the true native full
functional three-copy attachment, with no generated closure hull. -/
noncomputable def exactSevenTest : Finset Vertex :=
  SevenWalkLocality.test cycle

/-- The exact test has at most seven vertices, even without a
separate injectivity argument for the seven names. -/
theorem exactSevenTest_card_le_seven :
    exactSevenTest.card ≤ 7 :=
  SevenWalkLocality.test_card_le_seven cycle

/-- The exact test is truly function-closed in the ORIGINAL native
language, which has no function symbols. -/
theorem exactSevenTest_closed :
    Whole.toStructure.IsClosed (↑exactSevenTest : Set Vertex) :=
  SevenWalkLocality.test_closed Whole.toStructure cycle

/-- Seven genuine native attachment relation tuples survive the
same exact induced full-functional seven-vertex test. -/
theorem native_sevenWalk_edges :
    ∀ i : Fin 7,
      Whole.toStructure.rel () (fun k : Fin 2 =>
        if k = 0 then cycle i else
          cycle (SevenWalkLocality.next i)) := by
  intro i
  change Edge (cycle i) (cycle (SevenWalkLocality.next i))
  exact cycle_edge i

/-- The exact closed weak test cannot be two-coloured, independently
of how the unused ambient vertices are coloured. -/
theorem exactSevenTest_not_twoColorable :
    ¬ ∃ c : (↑exactSevenTest : Set Vertex) → Bool,
      ∀ x y : (↑exactSevenTest : Set Vertex),
        (SevenWalkLocality.small Whole.toStructure cycle).rel ()
          (fun k : Fin 2 => if k = 0 then x else y) →
        c x ≠ c y := by
  exact SevenWalkLocality.small_not_twoColorable
    Whole.toStructure cycle native_sevenWalk_edges

/-- The exact, closed <=7-vertex native C7 test has NO weak
source-defined homomorphism to the actual old P5. In particular,
a full/partial EHN projection of this test to the old P5 cannot
exist. This is stronger than the whole-stage no-hom theorem:
the obstruction is already witnessed by seven exact vertices. -/
theorem exactSevenTest_no_weak_hom_to_old :
    ¬ ∃ f : (↑exactSevenTest : Set Vertex) → Fin 5,
      (SevenWalkLocality.small Whole.toStructure cycle).
        IsWeakHomomorphism oldSystem.toStructure f := by
  apply SevenWalkLocality.small_no_weak_hom_to_bipartite
    Whole.toStructure cycle native_sevenWalk_edges oldSystem.toStructure
  refine ⟨oldColor, ?_⟩
  intro x y h
  change oldEdge x y at h
  exact oldColor_edge x y h

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7

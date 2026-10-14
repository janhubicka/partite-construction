import PartiteConstruction.Functional.NativeIteratedOriginalPartialAll
import PartiteConstruction.Functional.PublishedSparseningLoose
import PartiteConstruction.Functional.EHNProjectionGraphBridge
import PartiteConstruction.Functional.OriginalPartialWeakImage

/-!
# Published functional iteration with final irreducible B-copy extension

Only the ITERATED step is used; the native EHN recursive/induced partite
construction was already verified and is not repeated.

First perform the native n-pass genuine set-valued-function iteration.
This gives full Ramsey arrows, the original-2019 partial projection
and the controlled n-vertex STRICT RELATIONAL B-graph-tree witnesses.

Next use the independently checked projected-cover/loose-functional
completion ONCE, with the native output as its Ramsey control.
Its output is a genuine loose FULL-functional B-tree with every
irreducible inside an actual B-copy. Its weak EHN projection to the
n-pass stage is a graph homomorphism-embedding; the verified
LocallyTreeLike.witness_of_homEmbedding_image pulls the strict GRAPH
local-tree witnesses through this projection without increasing
the source's number of vertices. A-copy intersections remain controlled.
Compose the two original-partial projections to the original D.

This proves simultaneously the corrected global map, full Ramsey
arrow, original final B-extension (3), and the strong controlled
n-vertex graph-tree analogue of the published local property (2).
It does NOT turn those graph-tree completions into strict full
FUNCTION-language B-trees. The mixed reducible separator remains
the missing target-side assertion for that further strengthening.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Functional n-pass sparsening with genuine final irreducible B-copy
extension and preserved controlled RELATIONAL graph-tree bound.

The global projection is in the ORIGINAL 2019 partial-function
homomorphism-embedding sense (equivalent to EHN).
The final loose full-functional B-tree witnesses property (3), not
the still-open strict functional local-tree conclusion. -/
theorem sparseningRamsey_nativeFunctional_graphStrict_withBCover
    (K : StructureClass (L := L))
    (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      RelStructure.LocallyTreeLike A.graph B.graph C.graph n ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B W C ∧
      (∀ S : Finset W, S.card ≤ n →
        ∀ hS : C.IsClosed (↑S : Set W),
          RelStructure.HasTreeCompletion B.graph
            (C.induce (↑S : Set W) hS).graph) := by
  classical
  obtain ⟨X, hX, First, hFirstK, hFirstArrow, hFirstTree,
    _hFirstClosedTests, pFirst, hFirstProj⟩ :=
    inducedRamsey_nativeFunctionalIteration_originalPartial_all
      K hK A B D hKA hKB hpos κ hRamsey hA n hn
  letI : Finite X := hX
  obtain ⟨W, hW, C, hCK, hCArrow, pCov, hLoose,
      hCover, _hLocalLoose⟩ :=
    sparseningRamsey_functional_looseFullTrees_inClass
      K hK A B First hKA hKB κ hFirstArrow
  obtain ⟨p, hp⟩ := pCov
  have hPartial : IsOriginalPartialHomomorphismEmbedding
      C D (pFirst ∘ p) :=
    hFirstProj.comp hp.toOriginalPartial
  have hGraph : C.graph.IsHomomorphismEmbedding First.graph p :=
    hp.graphHomomorphismEmbedding
  have hLocal : RelStructure.LocallyTreeLike
      A.graph B.graph C.graph n := by
    intro S hCard
    have hImage : (S.image p).card ≤ n :=
      (Finset.card_image_le).trans hCard
    exact RelStructure.LocallyTreeLike.witness_of_homEmbedding_image
      (A := A.graph) (B := B.graph) (C := C.graph)
      hA.irreducible hFirstTree p hGraph S hImage
  let hWeak : WeakLocallyTreeCompletable B C n :=
    RelStructure.LocallyTreeCompletable.of_locallyTreeLike hLocal
  refine ⟨W, hW, C, hCK, hCArrow, ⟨pFirst ∘ p, hPartial⟩,
    hLocal, hCover, hLoose, ?_⟩
  intro S hCard hS
  exact hWeak.closedTest_graphCompletion S hCard hS

end StructuralRamsey.Structure

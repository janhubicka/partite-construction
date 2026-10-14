import PartiteConstruction.Functional.EHNCombinedInitialWeakTreeCover
import PartiteConstruction.Functional.EHNInvariantConstruction

/-!
# A complete native functional partite pass with BOTH published invariants

The actual initial picture satisfies (1) the corrected weak-vertex
function-GRAPH locally tree-like invariant and (2) the projected B-cover
property. A single genuine Hales--Jewett Picture step preserves both.
The original finite canonicalization and backward colour argument
can therefore be reused without constructing a second Ramsey pass.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}

/-- One full native induced Ramsey pass, with weak graph-tree control,
the projection to D, and projected irreducible B-cover on the SAME witness. -/
theorem inducedConstruction_weakTree_and_projectedCover
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph Base.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph Base.graph
        T.system.toStructure.graph n ∧
      T.ProjectedCover Base ∧
      Structure.Arrow A Base T.system.toStructure κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    RelStructure.LocallyTreeLike A.graph Base.graph
      T.system.toStructure.graph n ∧
    T.ProjectedCover Base
  have hInitial :
      ∀ β₀ : Structure.Embedding Base D,
        ∃ S : Stage K D,
          Q S ∧
          ∀ β : Structure.Embedding Base D,
            ∃ j : Structure.Embedding Base S.system.toStructure,
              ∀ x, S.system.part (j x) = β x := by
    intro β₀
    obtain ⟨S, hSTree, hSCov, hcopies⟩ :=
      initial_weakTree_and_projectedCover
        hK A Base hKB hA eAB hpos β₀ n hn hD
    exact ⟨S, ⟨hSTree, hSCov⟩, hcopies⟩
  have hStep :
      ∀ (S : Stage K D) (α : Structure.Embedding A D),
        Q S →
        ∃ R : Stage K D, Q R ∧ PictureProperty A S R α κ := by
    intro S α hS
    obtain ⟨R, hRTree, hRCov, hPicture⟩ :=
      pictureLemma_weakTree_and_projectedCover
        hK A hKA Base hA eAB S hS.2 α κ n hn hD hS.1
    exact ⟨R, ⟨hRTree, hRCov⟩, hPicture⟩
  obtain ⟨T, hBoth, hArrow⟩ :=
    inducedConstruction_preserving
      A Base D κ hRamsey Q hInitial hStep
  exact ⟨T, hBoth.1, hBoth.2, hArrow⟩

end StructuralRamsey.FunctionalPartite.EHN

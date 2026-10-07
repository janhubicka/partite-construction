import PartiteConstruction.Functional.ClosedPictureWeakTreeStep
import PartiteConstruction.Functional.ClosedConstruction
import PartiteConstruction.Iterated.WeakFunctionalTreeCompletion

/-! # Complete U-closed functional Picture trace with weak tree bounds

Each actual U-closed Hales--Jewett Picture construction carries the ordinary
weak-substructure graph-tree local bound, even though the set of possible
attaching maps is restricted to closed embeddings.  The same backwards
colour induction that proves the functional Ramsey theorem therefore has
a tree-completion invariant at every Picture stage.

The tree output is still a *relational graph-tree*: this theorem does not
infer target-side function-closure or strict functional tree amalgams.
-/

namespace StructuralRamsey.Partite.Closed.Construction

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}

/-- The actual finite U-closed Picture sequence preserves the complete
weak graph-tree local bound at a fixed size n. -/
theorem build_withWeakTree
    (A : RelStructure L.graph U)
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (S : Stage B D)
    [Finite U]
    (xs : List (RelevantEmbedding A B D))
    (κ : Type*) [Fintype κ]
    {VB : Type v}
    (Base : RelStructure L.graph VB)
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A Base)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := Base) id (n - 1))
    (hS : RelStructure.LocallyTreeCompletable
      Base S.system.toRelStructure n) :
    ∃ T : Stage B D,
      CanonicalOn A B D S.system T.system xs κ ∧
      RelStructure.LocallyTreeCompletable
        Base T.system.toRelStructure n := by
  induction xs with
  | nil =>
      refine ⟨S, ?_, hS⟩
      intro χ
      refine ⟨Partite.Closed.Embedding.id S.system, ?_⟩
      intro α h
      exact (List.not_mem_nil h).elim
  | cons α xs ih =>
      obtain ⟨T, hT, hTreeT⟩ := ih
      obtain ⟨Y, hY, C, hPartite, hU, hPicture, hTreeC⟩ :=
        Partite.Closed.Picture.pictureLemma_withLocal
          (A := A) (D := D) (B := T.system) (α := α.1)
          Base hA eAB n hn hD hTreeT
          T.isPartite T.uTransversal κ
      let R : Stage B D := {
        Vertex := Y
        finiteVertex := hY
        system := C
        isPartite := hPartite
        uTransversal := hU
      }
      refine ⟨R, ?_, hTreeC⟩
      intro χ
      obtain ⟨g, hg⟩ := hPicture (fun e => χ e.1)
      obtain ⟨f, hf⟩ := hT
        (fun e => χ (RelStructure.ClosedEmbedding.comp g.toRelClosed e))
      refine ⟨Partite.Closed.Embedding.comp g f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg
          (Partite.Closed.ProjectedEmbedding.comp e₁ f)
          (Partite.Closed.ProjectedEmbedding.comp e₂ f)
      · exact hf β hβ e₁ e₂


end StructuralRamsey.Partite.Closed.Construction

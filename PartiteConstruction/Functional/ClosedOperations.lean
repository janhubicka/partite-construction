import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Operations
import PartiteConstruction.Partite.Induced

/-! # U-closed restrictions of partite systems

If the selected copy A -> D is U-closed and P is D-partite, then the union of
parts over A is closed for all encoded function-output relations. This is the
formal content of Observation disaster1 in Appendix A.
-/
namespace StructuralRamsey.Partite.Closed

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P Q V : Type v}

/-- Parts lying over a U-closed embedded substructure form a U-closed subset. -/
theorem support_functionClosed
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (hB : B.IsPartiteOver D)
    (A : RelStructure L.graph Q)
    (α : RelStructure.ClosedEmbedding A D) :
    RelStructure.FunctionClosedSet B.toRelStructure
      (B.support α.toEmbedding.toFunctionEmbedding) := by
  classical
  intro F x y hy hx
  let αf : Q ↪ P := α.toEmbedding.toFunctionEmbedding
  have hargs : ∀ i, ∃ a : Q, B.part (x i) = α a := by
    intro i
    rcases hx i with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  choose a ha using hargs
  have hproj0 :=
    hB.1 (.inr F) (Structure.funcTuple x y) hy
  have htuple :
      B.part ∘ Structure.funcTuple x y =
        Structure.funcTuple (α ∘ a) (B.part y) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Structure.funcTuple]
    · simp [Structure.funcTuple, Function.comp_apply, ha]
  have hproj :
      D.rel (.inr F)
        (Structure.funcTuple (α ∘ a) (B.part y)) := by
    rw [← htuple]
    exact hproj0
  obtain ⟨z, hz, hzy⟩ := α.closed F a (B.part y) hproj
  exact ⟨z, hzy.symm⟩

/-- Inclusion of the restriction over a U-closed alpha is itself U-closed. -/
def restrictInclusion
    (D : RelStructure L.graph P)
    (B : Partite.System L.graph P V)
    (hB : B.IsPartiteOver D)
    (A : RelStructure L.graph Q)
    (α : RelStructure.ClosedEmbedding A D) :
    Embedding
      (B.restrict α.toEmbedding.toFunctionEmbedding) B :=
  ⟨Partite.System.inclusion B
      (B.support α.toEmbedding.toFunctionEmbedding),
    by
      intro F x y hy
      have hyS :=
        support_functionClosed D B hB A α F
          (Subtype.val ∘ x) y hy (fun i => (x i).2)
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      exact hy⟩

end StructuralRamsey.Partite.Closed

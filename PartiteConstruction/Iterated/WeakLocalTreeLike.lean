import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Weak local tree-likeness

For structures with set-valued functions the size induction is on weak
substructures, not closed substructures.  After graph encoding this is exactly
the existing relational local-tree-like predicate on arbitrary finite vertex
sets.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W : Type v}

/-- Function-language local tree-likeness measured on weak substructures. -/
def WeakLocallyTreeLike
    (A : Structure L U) (B : Structure L V)
    (C : Structure L W) (n : ℕ) : Prop :=
  RelStructure.LocallyTreeLike A.graph B.graph C.graph n

/-- Expanded formulation: every finite vertex set gives its weak induced
substructure, whose graph homomorphism-embeds into a tree amalgam of copies of
the graph of B, with the same A-copy control clause. -/
theorem weakLocallyTreeLike_iff
    (A : Structure L U) (B : Structure L V)
    (C : Structure L W) (n : ℕ) :
    WeakLocallyTreeLike A B C n ↔
      ∀ S : Finset W, S.card ≤ n →
        ∃ (Y : Type v) (T : RelStructure L.graph Y),
          RelStructure.TreeAmalgam B.graph Y T ∧
          ∃ f : ↥(↑S : Set W) → Y,
            ((C.weakInduce (↑S : Set W)).graph).
              IsHomomorphismEmbedding T f ∧
            ∀ α : RelStructure.Embedding A.graph C.graph,
              ∃ α' : RelStructure.Embedding A.graph T,
                ∀ a : U, ∀ ha : α a ∈ S,
                  ∃ a' : U, f ⟨α a, ha⟩ = α' a' := by
  constructor
  · intro h S hS
    obtain ⟨Y, T, hTree, f, hf, hctrl⟩ := h S hS
    refine ⟨Y, T, hTree, f, ?_, hctrl⟩
    exact hf.comp (weakGraphToInduce C (↑S : Set W)).isHomomorphismEmbedding
  · intro h S hS
    obtain ⟨Y, T, hTree, f, hf, hctrl⟩ := h S hS
    refine ⟨Y, T, hTree, f, ?_, hctrl⟩
    exact hf.comp (weakGraphFromInduce C (↑S : Set W)).isHomomorphismEmbedding

/-- Weak local tree-likeness is monotone in the size parameter. -/
theorem WeakLocallyTreeLike.mono
    {m n : ℕ}
    (h : WeakLocallyTreeLike A B C n) (hmn : m ≤ n) :
    WeakLocallyTreeLike A B C m :=
  RelStructure.LocallyTreeLike.mono h hmn

end StructuralRamsey.Structure

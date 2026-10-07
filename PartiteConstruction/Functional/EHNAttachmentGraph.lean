import PartiteConstruction.Structure.Attachment
import PartiteConstruction.Structure.Relationalize
import PartiteConstruction.Relational.Attachment

/-! # Genuine functional attachments and their relational graphs

Free attachment in the actual set-valued-function language agrees with
ordinary relational free attachment after graph encoding: a function value
is recorded as an ordinary incidence involving its inputs and output.

The supported overlap is *actually function-closed*, because the native
functional Picture uses genuine full embeddings. No U-closed graph-space
construction or repair is performed or needed.

This is a structural compatibility lemma, not a claim that a relational
tree completion can always be decoded to a full functional tree.
-/

namespace StructuralRamsey.Structure.Attachment

universe u v
variable {L : Language.{u}} {V W I : Type v}

/-- A genuine full attaching map also induces a relational graph embedding
on the weak graph-induced overlap on the same carrier. -/
def attachingGraphMap
    (B : Structure L V) (S : Set V) (hS : B.IsClosed S)
    (D : Structure L W)
    (f : Embedding (B.induce S hS) D) :
    RelStructure.Embedding (B.graph.induce S) D.graph where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R z
    have hInduce :
        (B.induce S hS).graph.rel R z ↔
          (B.graph.induce S).rel R z := by
      cases R with
      | inl _ => rfl
      | inr _ => rfl
    exact (f.graph.map_rel_iff R z).trans hInduce

/-- For a native functional attachment, the canonical fresh-copy vertex
has exactly the same tag as in the relational graph attachment. -/
theorem copyMap_graph_eq
    (B : Structure L V) (S : Set V) (hS : B.IsClosed S)
    (D : Structure L W)
    (f : I → Embedding (B.induce S hS) D)
    (i : I) (x : V) :
    copyMap B S hS D f i x =
      RelStructure.Attachment.copyMap
        B.graph S D.graph
        (fun j => attachingGraphMap B S hS D (f j)) i x := by
  classical
  by_cases hx : x ∈ S
  · rw [copyMap_mem (f := f) i x hx,
        RelStructure.Attachment.copyMap_mem
          (f := fun j => attachingGraphMap B S hS D (f j)) i x hx]
    rfl
  · rw [copyMap_not_mem (f := f) i x hx,
        RelStructure.Attachment.copyMap_not_mem
          (f := fun j => attachingGraphMap B S hS D (f j)) i x hx]

end StructuralRamsey.Structure.Attachment

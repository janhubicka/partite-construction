import PartiteConstruction.Relational.Attachment
import PartiteConstruction.Partite.Operations

/-! # Free attachment respecting a partition

This wrapper preserves the partition through the relational free attachment.
It supplies the extension operation used in the Picture Lemma.
-/
namespace StructuralRamsey.Partite.Attachment

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {W : Type z} {I : Type t}
variable (B : System L P V) (S : Set V) (D : System L P W)
variable (f : I → Embedding (B.induce S) D)

abbrev Vertex := RelStructure.Attachment.Vertex S (W := W) (I := I)

def part : Vertex S (W := W) (I := I) → P :=
  Sum.elim D.part (fun ix => B.part ix.2.val)

@[simp] theorem part_copyMap (i : I) (x : V) :
    part B S D (RelStructure.Attachment.copyMap B.toRelStructure S D.toRelStructure
      (fun i => (f i).toEmbedding) i x) = B.part x := by
  classical
  by_cases hx : x ∈ S
  · simpa [RelStructure.Attachment.copyMap, hx, part, System.induce] using (f i).map_part ⟨x, hx⟩
  · simp [RelStructure.Attachment.copyMap, hx, part]

noncomputable def attach : System L P (Vertex S (W := W) (I := I)) where
  toRelStructure := RelStructure.Attachment.attach B.toRelStructure S D.toRelStructure
    (fun i => (f i).toEmbedding)
  part := part B S D
  transversal R x hx k l hkl := by
    rcases hx with ⟨y, hy, rfl⟩ | ⟨i, y, hy, rfl⟩
    · exact congrArg Sum.inl (D.transversal R y hy k l hkl)
    · simp only [Function.comp_apply, part_copyMap] at hkl
      exact congrArg (RelStructure.Attachment.copyMap B.toRelStructure S D.toRelStructure
        (fun i => (f i).toEmbedding) i) (B.transversal R y hy k l hkl)

noncomputable def coreEmbedding : Embedding D (attach B S D f) where
  toEmbedding := RelStructure.Attachment.coreEmbedding B.toRelStructure S D.toRelStructure
    (fun i => (f i).toEmbedding)
  map_part _ := rfl

noncomputable def copyEmbedding (i : I) : Embedding B (attach B S D f) where
  toEmbedding := RelStructure.Attachment.copyEmbedding B.toRelStructure S D.toRelStructure
    (fun i => (f i).toEmbedding) i
  map_part := part_copyMap B S D f i

theorem copy_extends (i : I) (x : S) :
    copyEmbedding B S D f i x.val = coreEmbedding B S D f (f i x) :=
  RelStructure.Attachment.copy_extends B.toRelStructure S D.toRelStructure
    (fun i => (f i).toEmbedding) i x

end StructuralRamsey.Partite.Attachment

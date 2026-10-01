import PartiteConstruction.Partite.Basic

/-! # Restriction and injective relabelling of parts -/
namespace StructuralRamsey.Partite

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {Q : Type z}

namespace System

def induce (B : System L P V) (S : Set V) : System L P S where
  toRelStructure := B.toRelStructure.induce S
  part x := B.part x.val
  transversal R _ h i j hij := Subtype.ext (B.transversal R _ h i j hij)

def inclusion (B : System L P V) (S : Set V) : Embedding (B.induce S) B where
  toEmbedding := B.toRelStructure.inclusion S
  map_part _ := rfl

def relabel (B : System L P V) (α : P ↪ Q) : System L Q V where
  toRelStructure := B.toRelStructure
  part x := α (B.part x)
  transversal R x h i j hij := B.transversal R x h i j (α.injective hij)

def support (B : System L P V) (α : Q ↪ P) : Set V :=
  {x | B.part x ∈ Set.range α}

noncomputable def restrictedPart (B : System L P V) (α : Q ↪ P)
    (x : B.support α) : Q := Classical.choose x.property

@[simp] theorem restrictedPart_spec (B : System L P V) (α : Q ↪ P)
    (x : B.support α) : α (B.restrictedPart α x) = B.part x.val :=
  Classical.choose_spec x.property

/-- Keep the selected parts and name them by their preimages under α. -/
noncomputable def restrict (B : System L P V) (α : Q ↪ P) :
    System L Q (B.support α) where
  toRelStructure := B.toRelStructure.induce (B.support α)
  part := B.restrictedPart α
  transversal R x h i j hij := by
    apply Subtype.ext
    apply B.transversal R _ h i j
    exact (B.restrictedPart_spec α (x i)).symm.trans
      ((congrArg α hij).trans (B.restrictedPart_spec α (x j)))

end System

namespace Embedding

def relabel {B : System L P V} {W : Type*} {D : System L P W}
    (f : Embedding B D) (α : P ↪ Q) : Embedding (B.relabel α) (D.relabel α) where
  toEmbedding := f.toEmbedding
  map_part x := congrArg α (f.map_part x)

end Embedding

end StructuralRamsey.Partite

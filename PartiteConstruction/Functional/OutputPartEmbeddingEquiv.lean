import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Per-output-part singletonization is fully faithful for native embeddings

A genuine multivalued functional partite System B over a FIXED
part carrier P is exactly represented by its (F,q)-singleton split.
Every original function output y occurs in the unique split fibre
indexed by its actual part q=B.part y.

Conversely, any FULL PART-PRESERVING embedding of two canonical
split Systems preserves and REFLECTS entire original multivalued
function output fibres, by applying full split-fibre equality to
the q of the particular output under consideration.

Thus full native embeddings and full split-language embeddings
are equivalent, naturally under composition; and abstract
Ramsey arrows transport in both directions without any
vertex/rank changes or new Hales--Jewett alphabet letters.

This does NOT assert the corresponding statement for weak EHN
projections, which may not reflect source-undefined domains,
nor does it construct compatible TARGET B-tree completions.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v w z
variable {L : Language.{u}} {P : Type v}
variable {V : Type w} {W : Type z}

namespace Embedding

variable {A : System L P V} {B : System L P W}

/-- Recover the unique FULL original multivalued function embedding
from a FULL part-preserving embedding of the canonical singleton
output-part language.

Every target output y can be lifted by taking the split symbol
(F, B.part y), whose full fibre equality must hold for the given
embedding. This recovers ALL values, not merely domain activity. -/
def unsplitOutputParts
    (e : Embedding A.splitOutputParts B.splitOutputParts) :
    Embedding A B where
  toEmbedding := {
    toFun := e
    injective := e.toEmbedding.injective
    map_rel_iff := by
      intro R xs
      exact e.toEmbedding.map_rel_iff (ULift.up R) xs
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzSplit :
            z ∈ A.splitOutputParts.func
              ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), A.part z)
                xs := ⟨hz, rfl⟩
        have hImage :
            e z ∈ Structure.imageSet e
              (A.splitOutputParts.func
                ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), A.part z)
                xs) := ⟨z, hzSplit, rfl⟩
        rw [e.toEmbedding.map_func
          ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), A.part z)
          xs] at hImage
        exact hImage.1
      · intro hy
        let q : P := B.part y
        have hSplit :
            y ∈ B.splitOutputParts.func
              ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), q)
              (e ∘ xs) := ⟨hy, rfl⟩
        rw [← e.toEmbedding.map_func
          ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), q)
          xs] at hSplit
        obtain ⟨z, hz, hzy⟩ := hSplit
        exact ⟨z, hz.1, hzy⟩
  }
  map_part := e.map_part

/-- Full original multivalued partite embeddings and full
canonical per-output-part singleton embeddings are equivalent
on their actual underlying vertex maps.

No finiteness, order or positive-arity assumptions are needed. -/
def outputPartSplitEquiv :
    Embedding A B ≃
      Embedding A.splitOutputParts B.splitOutputParts where
  toFun := splitOutputParts
  invFun := unsplitOutputParts
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl

end Embedding

/-- Since canonical singletonization is bijective on FULL
PART-PRESERVING embeddings and commutes with composition,
abstract partite Ramsey arrows are invariant under this
change of function-language presentation.

All true multivalued function fibres are reconstructed;
this does not change the Hales--Jewett alphabet nor
the given finite Ramsey witness's carrier. -/
theorem arrow_iff_splitOutputParts
    {A : System L P V} {B : System L P W}
    {X : Type*} (C : System L P X) (κ : Type*) :
    Arrow A B C κ ↔
      Arrow A.splitOutputParts B.splitOutputParts C.splitOutputParts κ := by
  constructor
  · intro h χ
    obtain ⟨f, hf⟩ := h (fun e => χ e.splitOutputParts)
    refine ⟨f.splitOutputParts, ?_⟩
    intro e₁ e₂
    have h₁ :
        (f.comp e₁.unsplitOutputParts).splitOutputParts =
          f.splitOutputParts.comp e₁ := by
      apply Embedding.ext
      intro x
      rfl
    have h₂ :
        (f.comp e₂.unsplitOutputParts).splitOutputParts =
          f.splitOutputParts.comp e₂ := by
      apply Embedding.ext
      intro x
      rfl
    rw [← h₁, ← h₂]
    exact hf e₁.unsplitOutputParts e₂.unsplitOutputParts
  · intro h χ
    obtain ⟨f, hf⟩ := h (fun e => χ e.unsplitOutputParts)
    refine ⟨f.unsplitOutputParts, ?_⟩
    intro e₁ e₂
    have h₁ :
        (f.comp e₁.splitOutputParts).unsplitOutputParts =
          f.unsplitOutputParts.comp e₁ := by
      apply Embedding.ext
      intro x
      rfl
    have h₂ :
        (f.comp e₂.splitOutputParts).unsplitOutputParts =
          f.unsplitOutputParts.comp e₂ := by
      apply Embedding.ext
      intro x
      rfl
    rw [← h₁, ← h₂]
    exact hf e₁.splitOutputParts e₂.splitOutputParts

end StructuralRamsey.FunctionalPartite

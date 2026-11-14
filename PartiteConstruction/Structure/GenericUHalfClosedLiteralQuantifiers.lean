import PartiteConstruction.Structure.GenericUOriginalHalfClosedArrow

/-!
# Track F — literal half-closed input quantifiers versus explicit lift

The printed Appendix A hypothesis requires an ordinary (not U-closed)
embedding β:B→D such that every composite β∘e, for U-closed e:A→B,
is U-closed and all such composites are monochromatic.

The earlier verified OriginalUHalfClosedArrow packages the same information
using an auxiliary function `lift` assigning a U-closed embedding with
pointwise equality to β∘e. Here we eliminate `lift` and check the two
formulations are logically identical, not merely one-directional.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {T V P : Type v}

/-- Literal printed half-closed hypothesis: an ORDINARY B-copy with every
composite with a U-closed A-copy itself U-closed and monochromatic. -/
def OriginalUHalfClosedArrowLiteral
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) : Prop :=
  ∀ χ : {e : Embedding A D // IsUClosedEmbeddingRange U hU e} → κ,
    ∃ β : Embedding B D,
      ∃ hβ : ∀ e : {e : Embedding A B // IsUClosedEmbeddingRange U hU e},
        IsUClosedEmbeddingRange U hU (β.comp e.1),
        ∀ e₁ e₂ : {e : Embedding A B // IsUClosedEmbeddingRange U hU e},
          χ ⟨β.comp e₁.1, hβ e₁⟩ =
          χ ⟨β.comp e₂.1, hβ e₂⟩

/-- The auxiliary lift in the graph-transfer formulation is uniquely
determined by β and e by induced-embedding extensionality. Therefore it
does not strengthen the literal printed half-closed hypothesis. -/
theorem originalUHalfClosedArrowLiteral_iff
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) :
    OriginalUHalfClosedArrowLiteral A B D U hU κ ↔
      OriginalUHalfClosedArrow A B D U hU κ := by
  classical
  constructor
  · intro h χ
    obtain ⟨β, hβ, hm⟩ := h χ
    refine ⟨β, (fun e => ⟨β.comp e.1, hβ e⟩), ?_, ?_⟩
    · intro e x
      rfl
    · intro e₁ e₂
      exact hm e₁ e₂
  · intro h χ
    obtain ⟨β, lift, hlift, hm⟩ := h χ
    have hβ (e : {g : Embedding A B // IsUClosedEmbeddingRange U hU g}) :
        IsUClosedEmbeddingRange U hU (β.comp e.1) := by
      have heq : β.comp e.1 = (lift e).1 := by
        apply Embedding.ext
        intro x
        exact (hlift e x).symm
      rw [heq]
      exact (lift e).2
    refine ⟨β, hβ, ?_⟩
    intro e₁ e₂
    have heq (e : {g : Embedding A B // IsUClosedEmbeddingRange U hU g}) :
        (⟨β.comp e.1, hβ e⟩ :
          {g : Embedding A D // IsUClosedEmbeddingRange U hU g}) = lift e := by
      apply Subtype.ext
      apply Embedding.ext
      intro x
      exact (hlift e x).symm
    rw [heq e₁, heq e₂]
    exact hm e₁ e₂

end StructuralRamsey.RelStructure

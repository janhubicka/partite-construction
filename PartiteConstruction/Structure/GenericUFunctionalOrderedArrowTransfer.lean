import PartiteConstruction.Structure.GenericUFunctionalOrderedEquivalence

/-!
# Ordered Ramsey-arrow transfer for arbitrary nonredundant functional targets

The mixed functional Ramsey theorem already supplies a LINEARLY ORDERED
target. This proof preserves exactly the U-closed, strictly monotone
relational embeddings, including the full composition/colouring quantifiers.
Unlike the final survey wrapper, it does not restore the old named order;
that step is handled independently by the verified named-order reduct bridge.
-/

namespace StructuralRamsey
universe u v w z
namespace RelStructure

variable {L : RelLanguage.{u}}
variable {V : Type v} {W : Type w} {X : Type z}

/-- Literal ordered U-closed Ramsey arrow for a decoder of an arbitrary
function witness, using the genuine relational embedding compositions. -/
def OrderedUClosedArrowInto
    (A : RelStructure L V)
    (B : RelStructure L W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X)
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (κ : Type*) : Prop :=
  ∀ χ : OrderedUClosedEmbedding A (Structure.toRelU U hU C) U hU → κ,
    ∃ f : OrderedUClosedEmbedding B (Structure.toRelU U hU C) U hU,
      ∀ e₁ e₂ : OrderedUClosedEmbedding A B U hU,
        χ (orderedUClosedComp U hU f e₁) =
          χ (orderedUClosedComp U hU f e₂)

/-- If the genuine ordered functional A,B-structures have a Ramsey arrow
into an arbitrary ordered reduced functional C, its decode has exactly
the ordered U-closed arrow, on the identical witness vertex carrier. -/
theorem orderedUClosedArrowInto_of_functional
    (A : RelStructure L V)
    (B : RelStructure L W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X)
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (κ : Type*)
    (hRamsey :
      Structure.Arrow
        (A.asUFunctionsReduced U hU).withLinearOrder
        (B.asUFunctionsReduced U hU).withLinearOrder
        C.withLinearOrder κ) :
    OrderedUClosedArrowInto A B U hU C κ := by
  let EA := uClosedOrderedEmbeddingEquivIntoTarget A U hU C
  let EB := uClosedOrderedEmbeddingEquivIntoTarget B U hU C
  intro χ
  let χF : Structure.Embedding
      (A.asUFunctionsReduced U hU).withLinearOrder
      C.withLinearOrder → κ :=
    fun e => χ (EA.symm e)
  obtain ⟨f, hf⟩ := hRamsey χF
  refine ⟨EB.symm f, ?_⟩
  intro e₁ e₂
  let e₁F : Structure.Embedding
      (A.asUFunctionsReduced U hU).withLinearOrder
      (B.asUFunctionsReduced U hU).withLinearOrder :=
    (e₁.1.toReducedUFunctions U hU e₁.2.1).withExternalOrder e₁.2.2
  let e₂F : Structure.Embedding
      (A.asUFunctionsReduced U hU).withLinearOrder
      (B.asUFunctionsReduced U hU).withLinearOrder :=
    (e₂.1.toReducedUFunctions U hU e₂.2.1).withExternalOrder e₂.2.2
  have hc (e : OrderedUClosedEmbedding A B U hU) :
      EA.symm (f.comp
        ((e.1.toReducedUFunctions U hU e.2.1).withExternalOrder e.2.2)) =
        orderedUClosedComp U hU (EB.symm f) e := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  have hχ := hf e₁F e₂F
  change χ (EA.symm (f.comp e₁F)) =
    χ (EA.symm (f.comp e₂F)) at hχ
  change χ (orderedUClosedComp U hU (EB.symm f) e₁) =
    χ (orderedUClosedComp U hU (EB.symm f) e₂)
  rw [← hc e₁, ← hc e₂]
  exact hχ

end RelStructure
end StructuralRamsey

import PartiteConstruction.Structure.GenericUClosedPartiteEquivalence
import PartiteConstruction.Structure.GenericUOriginalOrderedArrow
import PartiteConstruction.Functional.ClosedPartite

/-!
# Track F — equivalence of the actual closed partite Ramsey arrows

The source language is an arbitrary relational L and a distinguished family
U of relations closed in the last output coordinate. The graph language
replaces those relations, rather than retaining duplicate symbols.

The real partite Ramsey arrows colour *closed induced part-preserving
embeddings*, not arbitrary homomorphisms. This module transports those
embedding TYPES and their literal compositions, hence all colourings,
between the original and graph encodings. Targets need no coherence
premise, and vertex carriers and part maps never change.

Dependent on the independently checked embedding Equiv in draft #604.
-/

namespace StructuralRamsey.Partite

universe u v

namespace OriginalUClosed

variable {L : RelLanguage.{u}} {P V W X : Type v}

/-- Actual original-language U-closed partite embeddings, as a subtype
of induced partite embeddings with U-closed range. -/
def Embedding (A : Partite.System L P V) (B : Partite.System L P W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) : Type _ :=
  {f : Partite.Embedding A B //
    RelStructure.IsUClosedEmbeddingRange U hU f.toEmbedding}

/-- Composition of the same original vertex and part maps is U-closed,
with no extra closure-hull construction. -/
def Embedding.comp
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : Partite.System L P V}
    {B : Partite.System L P W}
    {C : Partite.System L P X}
    (f : Embedding B C U hU)
    (e : Embedding A B U hU) : Embedding A C U hU := by
  let fe : {g : RelStructure.Embedding
      B.toRelStructure C.toRelStructure //
      RelStructure.IsUClosedEmbeddingRange U hU g} :=
    ⟨f.1.toEmbedding, f.2⟩
  let ee : {g : RelStructure.Embedding
      A.toRelStructure B.toRelStructure //
      RelStructure.IsUClosedEmbeddingRange U hU g} :=
    ⟨e.1.toEmbedding, e.2⟩
  have hc : RelStructure.IsUClosedEmbeddingRange U hU
      ((f.1.comp e.1).toEmbedding) :=
    (RelStructure.uClosedRangeComp U hU fe ee).2
  exact ⟨f.1.comp e.1, hc⟩

@[simp] theorem Embedding.comp_apply
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : Partite.System L P V}
    {B : Partite.System L P W}
    {C : Partite.System L P X}
    (f : Embedding B C U hU)
    (e : Embedding A B U hU) (x : V) :
    (Embedding.comp U hU f e).1 x = f.1 (e.1 x) := rfl

/-- Exact equality of the two actual composed graph embeddings, rather
than merely existence of an abstractly isomorphic copy. -/
theorem equiv_comp
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : Partite.System L P V}
    {B : Partite.System L P W}
    {C : Partite.System L P X}
    (f : Embedding B C U hU)
    (e : Embedding A B U hU) :
    (Partite.Embedding.uClosedReindexEquiv
      (A := A) (B := C) U hU)
        (Embedding.comp U hU f e) =
      Partite.Closed.Embedding.comp
        ((Partite.Embedding.uClosedReindexEquiv
          (A := B) (B := C) U hU) f)
        ((Partite.Embedding.uClosedReindexEquiv
          (A := A) (B := B) U hU) e) := by
  apply Partite.Closed.Embedding.ext
  intro x
  rfl

/-- The original Appendix A partite arrow with the *literal*
U-closed induced partite embeddings and their compositions. -/
def Arrow
    (A : Partite.System L P V)
    (B : Partite.System L P W)
    (C : Partite.System L P X)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) : Prop :=
  ∀ χ : Embedding A C U hU → κ,
    ∃ f : Embedding B C U hU,
      ∀ e₁ e₂ : Embedding A B U hU,
        χ (Embedding.comp U hU f e₁) =
          χ (Embedding.comp U hU f e₂)

/-- Same-target, same-vertex-colouring equivalence between the original
arbitrary-relational partite Ramsey arrow and the verified closed
function-graph partite arrow. -/
theorem arrow_iff_graph
    (A : Partite.System L P V)
    (B : Partite.System L P W)
    (C : Partite.System L P X)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) :
    Arrow A B C U hU κ ↔
      Partite.Closed.Arrow
        (A.asReducedUGraph U hU)
        (B.asReducedUGraph U hU)
        (C.asReducedUGraph U hU) κ := by
  let EA := Partite.Embedding.uClosedReindexEquiv
    (A := A) (B := C) U hU
  let EB := Partite.Embedding.uClosedReindexEquiv
    (A := B) (B := C) U hU
  let EAB := Partite.Embedding.uClosedReindexEquiv
    (A := A) (B := B) U hU
  constructor
  · intro h χG
    let χ : Embedding A C U hU → κ := fun e => χG (EA e)
    obtain ⟨f, hf⟩ := h χ
    refine ⟨EB f, ?_⟩
    intro g₁ g₂
    have hχ := hf (EAB.symm g₁) (EAB.symm g₂)
    change χG (EA (Embedding.comp U hU f (EAB.symm g₁))) =
      χG (EA (Embedding.comp U hU f (EAB.symm g₂))) at hχ
    have hc (g : Partite.Closed.Embedding
        (A.asReducedUGraph U hU) (B.asReducedUGraph U hU)) :
        EA (Embedding.comp U hU f (EAB.symm g)) =
          Partite.Closed.Embedding.comp (EB f) g := by
      apply Partite.Closed.Embedding.ext
      intro x
      rfl
    simpa only [hc] using hχ
  · intro h χ
    let χG : Partite.Closed.Embedding
        (A.asReducedUGraph U hU) (C.asReducedUGraph U hU) → κ :=
      fun g => χ (EA.symm g)
    obtain ⟨g, hg⟩ := h χG
    refine ⟨EB.symm g, ?_⟩
    intro e₁ e₂
    have hχ := hg (EAB e₁) (EAB e₂)
    change χ (EA.symm (Partite.Closed.Embedding.comp g (EAB e₁))) =
      χ (EA.symm (Partite.Closed.Embedding.comp g (EAB e₂))) at hχ
    have hc (e : Embedding A B U hU) :
        EA.symm (Partite.Closed.Embedding.comp g (EAB e)) =
          Embedding.comp U hU (EB.symm g) e := by
      apply Subtype.ext
      apply Partite.Embedding.ext
      intro x
      rfl
    simpa only [hc] using hχ

end OriginalUClosed
end StructuralRamsey.Partite

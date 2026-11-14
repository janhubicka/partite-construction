import PartiteConstruction.Structure.GenericUOrdinaryClosedEmbedding
import PartiteConstruction.Functional.HalfClosedConstruction

/-!
# Track F — original-relational half-closed arrow and exact graph equivalence

The survey's half-closed initial Ramsey hypothesis selects an ordinary
induced B-copy β:B→D (not necessarily U-closed), but every composite
β∘e with e an original U-closed A→B embedding must have a U-closed
lift with that literal underlying map, all of one colour.

This module identifies exactly that statement with the existing graph
RelStructure.HalfClosedArrow. Neither the ordinary B map nor the lift is
strengthened or weakened. Arbitrary relational L and positive U-arity.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {T V P : Type v}

/-- Literal original-language half-closed Ramsey hypothesis for an arbitrary
designated set U of last-output relations. -/
def OriginalUHalfClosedArrow
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) : Prop :=
  ∀ χ : {e : Embedding A D // IsUClosedEmbeddingRange U hU e} → κ,
    ∃ β : Embedding B D,
      ∃ lift : {e : Embedding A B // IsUClosedEmbeddingRange U hU e} →
          {e : Embedding A D // IsUClosedEmbeddingRange U hU e},
        (∀ e x, (lift e).1 x = β (e.1 x)) ∧
        ∀ e₁ e₂, χ (lift e₁) = χ (lift e₂)

namespace Embedding

/-- Ordinary induced embeddings also transport in both directions, with
no closure requirement: the underlying vertex injection is unchanged. -/
noncomputable def reducedUGraphEquiv
    {A : RelStructure L V} {B : RelStructure L P}
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    Embedding A B ≃
      Embedding (A.asReducedUGraph U hU) (B.asReducedUGraph U hU) where
  toFun e := e.asReducedUGraph U hU
  invFun e := e.ofReducedReindex U hU
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

/-- The half-closed Ramsey hypothesis is EXACTLY the graph-language
HalfClosedArrow; its ordinary B-copy and U-closed A-lifts are the same
literal vertex maps on both sides of the equivalence. -/
theorem originalUHalfClosedArrow_iff_graph
    (A : RelStructure L T)
    (B : RelStructure L V)
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) :
    OriginalUHalfClosedArrow A B D U hU κ ↔
      HalfClosedArrow
        (A.asReducedUGraph U hU)
        (B.asReducedUGraph U hU)
        (D.asReducedUGraph U hU) κ := by
  classical
  let EAD := Embedding.uClosedReducedGraphEquiv (A := A) (B := D) U hU
  let EAB := Embedding.uClosedReducedGraphEquiv (A := A) (B := B) U hU
  let EBD := Embedding.reducedUGraphEquiv (A := B) (B := D) U hU
  constructor
  · intro h χ_g
    let χ : {e : Embedding A D // IsUClosedEmbeddingRange U hU e} → κ :=
      fun e => χ_g (EAD e)
    obtain ⟨β, lift, hlift, hmono⟩ := h χ
    refine ⟨EBD β, (fun e => EAD (lift (EAB.symm e))), ?_, ?_⟩
    · intro e x
      exact hlift (EAB.symm e) x
    · intro e₁ e₂
      exact hmono (EAB.symm e₁) (EAB.symm e₂)
  · intro h χ
    let χ_g : ClosedEmbedding
        (A.asReducedUGraph U hU) (D.asReducedUGraph U hU) → κ :=
      fun e => χ (EAD.symm e)
    obtain ⟨β, lift, hlift, hmono⟩ := h χ_g
    refine ⟨EBD.symm β, (fun e => EAD.symm (lift (EAB e))), ?_, ?_⟩
    · intro e x
      exact hlift (EAB e) x
    · intro e₁ e₂
      exact hmono (EAB e₁) (EAB e₂)

end StructuralRamsey.RelStructure

import PartiteConstruction.Functional.HalfClosedConstruction

/-! # Unary part predicates for languages with functions

The recursive construction repeatedly switches between a partite-system view
and the manuscript's L_P expansion by unary predicates naming the parts.  This
file provides that interface for graph encodings of set-valued functions.

The added language keeps universe-lifted copies of the original relation and
function symbols and adds one unary relation symbol for every part.
Consequently U-closedness is unchanged, while relational embeddings of the
expansion are exactly part-preserving embeddings of the original partite
systems.
-/
namespace StructuralRamsey

universe u v

namespace Language

/-- Add unary relation symbols naming the parts.  Old symbols are universe
lifted so the part type may live in a larger carrier universe. -/
def withParts (L : Language.{u}) (P : Type v) : Language.{max u v} where
  RelSymbol := ULift.{max u v, u} L.RelSymbol ⊕ P
  FuncSymbol := ULift.{max u v, u} L.FuncSymbol
  relArity
    | .inl R => L.relArity R.down
    | .inr _ => 1
  funcArity F := L.funcArity F.down

@[simp] theorem withParts_relArity_left
    (L : Language.{u}) (P : Type v) (R : L.RelSymbol) :
    (L.withParts P).relArity (.inl (ULift.up R)) = L.relArity R := rfl

@[simp] theorem withParts_relArity_right
    (L : Language.{u}) (P : Type v) (p : P) :
    (L.withParts P).relArity (.inr p) = 1 := rfl

@[simp] theorem withParts_funcArity
    (L : Language.{u}) (P : Type v) (F : L.FuncSymbol) :
    (L.withParts P).funcArity (ULift.up F) = L.funcArity F := rfl


/-- Positive function arity is unchanged by adding part predicates. -/
theorem PositiveFuncArity.withParts
    {L : Language.{u}} {P : Type v}
    (h : L.PositiveFuncArity) :
    (L.withParts P).PositiveFuncArity := by
  intro F
  exact h F.down

end Language

namespace Partite

open RelStructure Structure

variable {L : Language.{u}} {P V W X : Type v}

/-- Expand a graph-partite system by unary predicates naming its parts. -/
def System.expandFunctional (B : System L.graph P V) :
    RelStructure (L.withParts P).graph V where
  rel
    | .inl (.inl R), x => B.rel (.inl R.down) x
    | .inl (.inr p), x => B.part (x ⟨0, Nat.zero_lt_one⟩) = p
    | .inr F, x => B.rel (.inr F.down) x

/-- Forget the unary part predicates, keeping the same carrier and an arbitrary
part map. -/
def System.ofFunctionalExpansion
    {Q : Type v}
    (C : System (L.withParts P).graph Q V) :
    System L.graph Q V where
  rel
    | .inl R, x => C.rel (.inl (.inl (ULift.up R))) x
    | .inr F, x => C.rel (.inr (ULift.up F)) x
  part := C.part
  transversal := by
    intro R x hx i j hp
    cases R with
    | inl R =>
        exact C.transversal (.inl (.inl (ULift.up R))) x hx i j hp
    | inr F =>
        exact C.transversal (.inr (ULift.up F)) x hx i j hp

namespace Embedding

variable {A : System L.graph P V} {B : System L.graph P W}

/-- A part-preserving embedding becomes an embedding of the unary-predicate
expansions. -/
def expandFunctional (f : Partite.Embedding A B) :
    RelStructure.Embedding A.expandFunctional B.expandFunctional where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        cases R with
        | inl R => exact f.map_rel_iff (.inl R.down) x
        | inr p =>
            change (B.part (f (x (0 : Fin 1))) = p) ↔
              (A.part (x (0 : Fin 1)) = p)
            rw [f.map_part]
    | inr F =>
        exact f.map_rel_iff (.inr F.down) x

/-- Recover a part-preserving embedding from the unary-predicate expansion. -/
def ofFunctionalExpanded
    (f : RelStructure.Embedding A.expandFunctional B.expandFunctional) :
    Partite.Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        exact f.map_rel_iff (.inl (.inl (ULift.up R))) x
    | inr F =>
        exact f.map_rel_iff (.inr (ULift.up F)) x
  map_part x :=
    (f.map_rel_iff
      (.inl (.inr (A.part x))) (fun _ => x)).mpr rfl

def functionalExpandedEquiv :
    Partite.Embedding A B ≃
      RelStructure.Embedding A.expandFunctional B.expandFunctional where
  toFun := expandFunctional
  invFun := ofFunctionalExpanded
  left_inv := by
    intro f
    apply Partite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply RelStructure.Embedding.ext
    intro x
    rfl

end Embedding

namespace Closed.Embedding

variable {A : System L.graph P V} {B : System L.graph P W}

/-- A closed partite embedding becomes a closed embedding of the
unary-predicate expansions. -/
def expandFunctional (f : Partite.Closed.Embedding A B) :
    RelStructure.ClosedEmbedding A.expandFunctional B.expandFunctional where
  toEmbedding := f.1.expandFunctional
  closed := by
    intro F x y hy
    exact f.2 F.down x y hy

/-- Recover a closed partite embedding from the unary-predicate expansion. -/
def ofFunctionalExpanded
    (f : RelStructure.ClosedEmbedding A.expandFunctional B.expandFunctional) :
    Partite.Closed.Embedding A B := by
  let pe : Partite.Embedding A B :=
    Partite.Embedding.ofFunctionalExpanded f.toEmbedding
  refine ⟨pe, ?_⟩
  intro F x y hy
  exact f.closed (ULift.up F) x y hy

def functionalExpandedEquiv :
    Partite.Closed.Embedding A B ≃
      RelStructure.ClosedEmbedding A.expandFunctional B.expandFunctional where
  toFun := expandFunctional
  invFun := ofFunctionalExpanded
  left_inv := by
    intro f
    apply Partite.Closed.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl

end Closed.Embedding

/-- Closed Ramsey arrows are invariant under adding the unary part predicates. -/
theorem closedArrow_iff_functionalExpanded
    {A : System L.graph P V} {B : System L.graph P W}
    {C : System L.graph P X} {κ : Type*} :
    Partite.Closed.Arrow A B C κ ↔
      RelStructure.ClosedArrow
        A.expandFunctional B.expandFunctional C.expandFunctional κ := by
  constructor
  · intro h χ
    obtain ⟨f, hf⟩ :=
      h (fun e => χ e.expandFunctional)
    refine ⟨f.expandFunctional, ?_⟩
    intro e₁ e₂
    exact hf
      (Partite.Closed.Embedding.ofFunctionalExpanded e₁)
      (Partite.Closed.Embedding.ofFunctionalExpanded e₂)
  · intro h χ
    obtain ⟨f, hf⟩ :=
      h (fun e =>
        χ (Partite.Closed.Embedding.ofFunctionalExpanded e))
    refine ⟨Partite.Closed.Embedding.ofFunctionalExpanded f, ?_⟩
    intro e₁ e₂
    exact hf e₁.expandFunctional e₂.expandFunctional


/-- Native partite form of the half-closed Ramsey hypothesis. -/
def HalfClosedArrow
    {A : System L.graph P V}
    {B : System L.graph P W}
    {D : System L.graph P X}
    (κ : Type*) : Prop :=
  ∀ χ : Partite.Closed.Embedding A D → κ,
    ∃ β : Partite.Embedding B D,
      ∃ lift :
          Partite.Closed.Embedding A B →
            Partite.Closed.Embedding A D,
        (∀ e x, lift e x = β (e x)) ∧
        ∀ e₁ e₂, χ (lift e₁) = χ (lift e₂)

/-- The native partite half-closed arrow is exactly the relational
half-closed arrow of the unary-predicate expansions. -/
theorem halfClosedArrow_iff_functionalExpanded
    {A : System L.graph P V}
    {B : System L.graph P W}
    {D : System L.graph P X}
    {κ : Type*} :
    Partite.HalfClosedArrow (A := A) (B := B) (D := D) κ ↔
      RelStructure.HalfClosedArrow
        A.expandFunctional B.expandFunctional D.expandFunctional κ := by
  constructor
  · intro h χ
    let χ' : Partite.Closed.Embedding A D → κ :=
      fun e => χ e.expandFunctional
    obtain ⟨β, lift, hmap, hmono⟩ := h χ'
    let β' : RelStructure.Embedding
        B.expandFunctional D.expandFunctional :=
      β.expandFunctional
    let lift' :
        RelStructure.ClosedEmbedding
            A.expandFunctional B.expandFunctional →
          RelStructure.ClosedEmbedding
            A.expandFunctional D.expandFunctional :=
      fun e =>
        (lift
          (Partite.Closed.Embedding.ofFunctionalExpanded e)).expandFunctional
    refine ⟨β', lift', ?_, ?_⟩
    · intro e x
      change
        lift (Partite.Closed.Embedding.ofFunctionalExpanded e) x =
          β (Partite.Closed.Embedding.ofFunctionalExpanded e x)
      exact hmap _ x
    · intro e₁ e₂
      exact hmono
        (Partite.Closed.Embedding.ofFunctionalExpanded e₁)
        (Partite.Closed.Embedding.ofFunctionalExpanded e₂)
  · intro h χ
    let χ' :
        RelStructure.ClosedEmbedding
          A.expandFunctional D.expandFunctional → κ :=
      fun e =>
        χ (Partite.Closed.Embedding.ofFunctionalExpanded e)
    obtain ⟨β, lift, hmap, hmono⟩ := h χ'
    let β' : Partite.Embedding B D :=
      Partite.Embedding.ofFunctionalExpanded β
    let lift' :
        Partite.Closed.Embedding A B →
          Partite.Closed.Embedding A D :=
      fun e =>
        Partite.Closed.Embedding.ofFunctionalExpanded
          (lift e.expandFunctional)
    refine ⟨β', lift', ?_, ?_⟩
    · intro e x
      change lift e.expandFunctional x = β e.expandFunctional x
      exact hmap _ x
    · intro e₁ e₂
      exact hmono e₁.expandFunctional e₂.expandFunctional

/-- U-transversality is unchanged when forgetting the unary part predicates. -/
theorem functionOutputTransversal_of_expanded
    {Q : Type v}
    (C : System (L.withParts P).graph Q V)
    (h : C.FunctionOutputTransversal) :
    (C.ofFunctionalExpansion).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  exact h (ULift.up F) x y z hy hz hp

end Partite
end StructuralRamsey

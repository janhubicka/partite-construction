import PartiteConstruction.Functional.HalfClosedConstruction
import PartiteConstruction.Functional.NestedFlatten

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
      change lift e.expandFunctional x = β (e x)
      exact hmap _ x
    · intro e₁ e₂
      exact hmono e₁.expandFunctional e₂.expandFunctional


/-- Irreducibility of the original graph reduct implies irreducibility after
adding unary part predicates, since the original witnessing relation tuple is
still present. -/
theorem irreducible_expandFunctional_of_reduct
    {Q : Type v}
    (C : System (L.withParts P).graph Q V)
    (S : Set V)
    (hS : ((C.ofFunctionalExpansion).toRelStructure.induce S).Irreducible) :
    (C.toRelStructure.induce S).Irreducible := by
  intro x y hxy
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
  cases R with
  | inl R =>
      exact ⟨.inl (.inl (ULift.up R)), z, i, j, hz, hzi, hzj⟩
  | inr F =>
      exact ⟨.inr (ULift.up F), z, i, j, hz, hzi, hzj⟩

/-- If an expanded-language partite system projects homomorphism-embedding-wise
to the unary-predicate expansion of D, then forgetting the unary predicates
leaves an ordinary D-partite system. -/
theorem isPartiteOver_of_functionalExpanded
    {Q : Type v}
    (D : System L.graph P Q)
    (C : System (L.withParts P).graph Q V)
    (hC : C.IsPartiteOver D.expandFunctional) :
    (C.ofFunctionalExpansion).IsPartiteOver D.toRelStructure := by
  constructor
  · intro R x hx
    cases R with
    | inl R =>
        exact hC.1 (.inl (.inl (ULift.up R))) x hx
    | inr F =>
        exact hC.1 (.inr (ULift.up F)) x hx
  · intro S hS
    have hSexp :
        (C.toRelStructure.induce S).Irreducible :=
      irreducible_expandFunctional_of_reduct C S hS
    obtain ⟨e, he⟩ := hC.embeddingOn S hSexp
    let d : RelStructure.Embedding
        ((C.ofFunctionalExpansion).toRelStructure.induce S)
        D.toRelStructure := {
      toFun := e
      injective := e.injective
      map_rel_iff := by
        intro R x
        cases R with
        | inl R =>
            exact e.map_rel_iff (.inl (.inl (ULift.up R))) x
        | inr F =>
            exact e.map_rel_iff (.inr (ULift.up F)) x
    }
    exact ⟨d, he⟩

/-- U-transversality is unchanged when forgetting the unary part predicates. -/
theorem functionOutputTransversal_of_expanded
    {Q : Type v}
    (C : System (L.withParts P).graph Q V)
    (h : C.FunctionOutputTransversal) :
    (C.ofFunctionalExpansion).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  exact h (ULift.up F) x y z hy hz hp


/-- A closed embedding of an L_P expansion into a nested system becomes a
closed partite embedding after forgetting the unary predicates and flattening
the nested partition back to the outer part set. -/
def Closed.Embedding.toFlattenedFunctional
    {U Y : Type v}
    (A : System L.graph P U)
    (D : System L.graph P X)
    (C : System (L.withParts P).graph X Y)
    (hC : C.IsPartiteOver D.expandFunctional)
    (e : RelStructure.ClosedEmbedding
      A.expandFunctional C.toRelStructure) :
    Partite.Closed.Embedding A
      (Nested.flatten D C.ofFunctionalExpansion
        (isPartiteOver_of_functionalExpanded D C hC)) := by
  let C0 := C.ofFunctionalExpansion
  let hC0 : C0.IsPartiteOver D.toRelStructure :=
    isPartiteOver_of_functionalExpanded D C hC
  let T := Nested.flatten D C0 hC0
  let pe : Partite.Embedding A T := {
    toFun := e
    injective := e.toEmbedding.injective
    map_rel_iff := by
      intro R x
      cases R with
      | inl R =>
          exact e.toEmbedding.map_rel_iff
            (.inl (.inl (ULift.up R))) x
      | inr F =>
          exact e.toEmbedding.map_rel_iff
            (.inr (ULift.up F)) x
    map_part := by
      intro a
      have hsrc :
          A.expandFunctional.rel
            (.inl (.inr (A.part a))) (fun _ => a) := rfl
      have hmid :
          C.rel (.inl (.inr (A.part a)))
            (e ∘ (fun _ : Fin 1 => a)) :=
        (e.toEmbedding.map_rel_iff
          (.inl (.inr (A.part a))) (fun _ : Fin 1 => a)).mpr hsrc
      have hout :=
        hC.1 (.inl (.inr (A.part a)))
          (e ∘ (fun _ : Fin 1 => a)) hmid
      change D.part (C.part (e a)) = A.part a at hout
      exact hout
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  exact e.closed (ULift.up F) x y hy

/-- A closed Ramsey arrow in the L_P expansion descends to the flattened
partite target. -/
theorem closedArrow_flattened_of_functionalExpanded
    {U Y : Type v}
    (A : System L.graph P U)
    (B : System L.graph P W)
    (D : System L.graph P X)
    (C : System (L.withParts P).graph X Y)
    (hC : C.IsPartiteOver D.expandFunctional)
    (κ : Type*)
    (hArrow :
      RelStructure.ClosedArrow
        A.expandFunctional B.expandFunctional C.toRelStructure κ) :
    Partite.Closed.Arrow A B
      (Nested.flatten D C.ofFunctionalExpansion
        (isPartiteOver_of_functionalExpanded D C hC)) κ := by
  intro χ
  let lowerA :
      RelStructure.ClosedEmbedding
        A.expandFunctional C.toRelStructure →
      Partite.Closed.Embedding A
        (Nested.flatten D C.ofFunctionalExpansion
          (isPartiteOver_of_functionalExpanded D C hC)) :=
    fun e =>
      Partite.Closed.Embedding.toFlattenedFunctional A D C hC e
  let θ :
      RelStructure.ClosedEmbedding
        A.expandFunctional C.toRelStructure → κ :=
    fun e => χ (lowerA e)
  obtain ⟨f, hf⟩ := hArrow θ
  let fg :
      Partite.Closed.Embedding B
        (Nested.flatten D C.ofFunctionalExpansion
          (isPartiteOver_of_functionalExpanded D C hC)) :=
    Partite.Closed.Embedding.toFlattenedFunctional B D C hC f
  refine ⟨fg, ?_⟩
  intro e₁ e₂
  have hh := hf e₁.expandFunctional e₂.expandFunctional
  have h₁ :
      lowerA (RelStructure.ClosedEmbedding.comp
        f e₁.expandFunctional) =
      Partite.Closed.Embedding.comp fg e₁ := by
    apply Partite.Closed.Embedding.ext
    intro x
    change f (e₁ x) = f (e₁ x)
    rfl
  have h₂ :
      lowerA (RelStructure.ClosedEmbedding.comp
        f e₂.expandFunctional) =
      Partite.Closed.Embedding.comp fg e₂ := by
    apply Partite.Closed.Embedding.ext
    intro x
    change f (e₂ x) = f (e₂ x)
    rfl
  change
    χ (Partite.Closed.Embedding.comp fg e₁) =
      χ (Partite.Closed.Embedding.comp fg e₂)
  change
    χ (lowerA (RelStructure.ClosedEmbedding.comp
      f e₁.expandFunctional)) =
      χ (lowerA (RelStructure.ClosedEmbedding.comp
        f e₂.expandFunctional)) at hh
  rw [h₁, h₂] at hh
  exact hh

end Partite
end StructuralRamsey

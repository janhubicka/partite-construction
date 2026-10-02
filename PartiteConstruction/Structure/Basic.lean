import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Structures with relations and set-valued functions

This is the survey's ambient notion of language and structure.  Function
symbols are genuinely set-valued: a symbol F of arity n is interpreted as a
map V^n -> Set V.  Homomorphisms preserve relations and carry every function
value set *onto* the corresponding target value set.
-/
namespace StructuralRamsey

universe u v w z

structure Language where
  RelSymbol : Type u
  FuncSymbol : Type u
  relArity : RelSymbol → ℕ
  funcArity : FuncSymbol → ℕ

structure Structure (L : Language.{u}) (V : Type v) where
  rel : (R : L.RelSymbol) → (Fin (L.relArity R) → V) → Prop
  func : (F : L.FuncSymbol) → (Fin (L.funcArity F) → V) → Set V

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w} {X : Type z}

/-- Image of a set under a map, written pointwise for function preservation. -/
def imageSet (f : V → W) (S : Set V) : Set W := f '' S

/-- Survey homomorphism: relations are preserved and set-valued functions are
mapped *onto* the corresponding value set. -/
def IsHomomorphism (A : Structure L V) (B : Structure L W)
    (f : V → W) : Prop :=
  (∀ R x, A.rel R x → B.rel R (f ∘ x)) ∧
  (∀ F x, imageSet f (A.func F x) = B.func F (f ∘ x))

/-- Embeddings are injective homomorphisms which also reflect relations.
For set-valued functions, equality of value sets in the homomorphism condition
already supplies the required inverse preservation on the image. -/
structure Embedding (A : Structure L V) (B : Structure L W) where
  toFun : V → W
  injective : Function.Injective toFun
  map_rel_iff : ∀ R x, B.rel R (toFun ∘ x) ↔ A.rel R x
  map_func : ∀ F x, imageSet toFun (A.func F x) = B.func F (toFun ∘ x)

instance {A : Structure L V} {B : Structure L W} :
    CoeFun (Embedding A B) (fun _ => V → W) := ⟨Embedding.toFun⟩

namespace Embedding

variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  exact funext h

def id (A : Structure L V) : Embedding A A where
  toFun := _root_.id
  injective := Function.injective_id
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩

def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toFun := g ∘ f
  injective := g.injective.comp f.injective
  map_rel_iff R x := (g.map_rel_iff R (f ∘ x)).trans (f.map_rel_iff R x)
  map_func := by
    intro F x
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hfa : f a ∈ B.func F (f ∘ x) := by
        have h : f a ∈ imageSet f (A.func F x) := ⟨a, ha, rfl⟩
        rw [f.map_func F x] at h
        exact h
      have hga : g (f a) ∈ C.func F (g ∘ (f ∘ x)) := by
        have h : g (f a) ∈ imageSet g (B.func F (f ∘ x)) :=
          ⟨f a, hfa, rfl⟩
        rw [g.map_func F (f ∘ x)] at h
        exact h
      simpa [Function.comp_assoc] using hga
    · intro hz
      have hz' : z ∈ C.func F (g ∘ (f ∘ x)) := by
        simpa [Function.comp_assoc] using hz
      rw [← g.map_func F (f ∘ x)] at hz'
      rcases hz' with ⟨b, hb, rfl⟩
      rw [← f.map_func F x] at hb
      rcases hb with ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩

@[simp] theorem comp_apply (g : Embedding B C) (f : Embedding A B) (x : V) :
    g.comp f x = g (f x) := rfl

theorem isHomomorphism (f : Embedding A B) : A.IsHomomorphism B f := by
  constructor
  · intro R x hx
    exact (f.map_rel_iff R x).mpr hx
  · exact f.map_func

instance [Finite V] [Finite W] : Finite (Embedding A B) :=
  Finite.of_injective Embedding.toFun (fun _ _ h => ext (congrFun h))

end Embedding

/-- A subset is closed under every set-valued function. -/
def IsClosed (A : Structure L V) (S : Set V) : Prop :=
  ∀ F x, (∀ i, x i ∈ S) → A.func F x ⊆ S

/-- Structure induced on a closed subset. -/
def induce (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    Structure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := {y | y.1 ∈ A.func F (Subtype.val ∘ x)}

def inclusion (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    Embedding (A.induce S hS) A where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyS : y ∈ S := hS F (Subtype.val ∘ x)
        (fun i => (x i).2) hy
      exact ⟨⟨y, hyS⟩, hy, rfl⟩

/-- Structural Ramsey arrow for full relation/function structures. -/
def Arrow (A : Structure L V) (B : Structure L W)
    {Y : Type*} (C : Structure L Y) (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C,
    ∀ e₁ e₂ : Embedding A B, χ (f.comp e₁) = χ (f.comp e₂)

end Structure
end StructuralRamsey

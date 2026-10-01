import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Relational structures and induced embeddings

The first layer is independent of partite systems and finiteness. A relation
symbol has a specified finite arity. Repeated entries and nullary relations
are allowed. Later developments with functions can reuse the relational reduct.
-/

namespace StructuralRamsey

universe u v w z

structure RelLanguage where
  Symbol : Type u
  arity : Symbol → ℕ

structure RelStructure (L : RelLanguage.{u}) (V : Type v) where
  rel : (R : L.Symbol) → (Fin (L.arity R) → V) → Prop

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w} {X : Type z}

/-- Induced embeddings: both positive and negative relation information is kept. -/
structure Embedding (A : RelStructure L V) (B : RelStructure L W) where
  toFun : V → W
  injective : Function.Injective toFun
  map_rel_iff : ∀ R x, B.rel R (toFun ∘ x) ↔ A.rel R x

instance {A : RelStructure L V} {B : RelStructure L W} :
    CoeFun (Embedding A B) (fun _ => V → W) := ⟨Embedding.toFun⟩

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W} {C : RelStructure L X}

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; simp_all only [mk.injEq]; exact funext h

def id (A : RelStructure L V) : Embedding A A where
  toFun := _root_.id
  injective := Function.injective_id
  map_rel_iff := fun _ _ => Iff.rfl

def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toFun := g ∘ f
  injective := g.injective.comp f.injective
  map_rel_iff R x := (g.map_rel_iff R (f ∘ x)).trans (f.map_rel_iff R x)

@[simp] theorem comp_apply (g : Embedding B C) (f : Embedding A B) (x : V) :
    g.comp f x = g (f x) := rfl

@[simp] theorem id_apply (x : V) : id A x = x := rfl

@[simp] theorem id_comp (f : Embedding A B) : (id B).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : Embedding A B) : f.comp (id A) = f := by ext; rfl

theorem comp_assoc {Y : Type*} {D : RelStructure L Y}
    (h : Embedding C D) (g : Embedding B C) (f : Embedding A B) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

instance [Finite V] [Finite W] : Finite (Embedding A B) :=
  Finite.of_injective Embedding.toFun (fun _ _ h => ext (congrFun h))

end Embedding

/-- The structure induced on a subset, including all repeated-entry tuples. -/
def induce (A : RelStructure L V) (S : Set V) : RelStructure L S where
  rel R x := A.rel R (Subtype.val ∘ x)

def inclusion (A : RelStructure L V) (S : Set V) : Embedding (A.induce S) A where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := fun _ _ => Iff.rfl

end RelStructure
end StructuralRamsey

import PartiteConstruction.Ramsey.Basic

/-! # Partite systems

A partition map packages the added unary predicates. Transversality forbids
distinct vertices in one part in a relation tuple; it does NOT forbid repeated
occurrences of the same vertex (Appendix A's convention).
-/
namespace StructuralRamsey.Partite

open RelStructure

universe u v w z

structure System (L : RelLanguage.{u}) (P : Type v) (V : Type w)
    extends RelStructure L V where
  part : V → P
  transversal : ∀ R x, rel R x → ∀ i j, part (x i) = part (x j) → x i = x j

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {U : Type z}

/-- The transversal system with exactly one vertex in every part. -/
def transversal (A : RelStructure L P) : System L P P where
  toRelStructure := A
  part := id
  transversal := fun _ _ _ _ _ h => h

structure Embedding (A : System L P V) (B : System L P U)
    extends RelStructure.Embedding A.toRelStructure B.toRelStructure where
  map_part : ∀ x, B.part (toFun x) = A.part x

instance {A : System L P V} {B : System L P U} :
    CoeFun (Embedding A B) (fun _ => V → U) := ⟨fun f => f.toEmbedding.toFun⟩

namespace Embedding

variable {A : System L P V} {B : System L P U}

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  exact RelStructure.Embedding.ext h

def id (A : System L P V) : Embedding A A where
  toEmbedding := RelStructure.Embedding.id A.toRelStructure
  map_part := fun _ => rfl

def comp {X : Type*} {C : System L P X}
    (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toEmbedding := g.toEmbedding.comp f.toEmbedding
  map_part x := (g.map_part (f x)).trans (f.map_part x)

@[simp] theorem comp_apply {X : Type*} {C : System L P X}
    (g : Embedding B C) (f : Embedding A B) (x : V) : g.comp f x = g (f x) := rfl

instance [Finite V] [Finite U] : Finite (Embedding A B) :=
  Finite.of_injective (fun f => f.toEmbedding)
    (fun _ _ h => ext (fun x => congrArg (fun e : RelStructure.Embedding _ _ => e x) h))

end Embedding

def Arrow (A : System L P V) (B : System L P U)
    {X : Type*} (C : System L P X) (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C,
    ∀ e₁ e₂ : Embedding A B, χ (f.comp e₁) = χ (f.comp e₂)

end StructuralRamsey.Partite

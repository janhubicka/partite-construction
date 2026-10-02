import PartiteConstruction.Structure.Basic

/-! # Partite systems with set-valued functions

The relational transversality condition is supplemented by function-output
transversality: two values of one function application lying in the same part
must coincide.  This is the invariant needed by coordinatewise powers with
genuinely set-valued functions.
-/
namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} {V : Type w} {W : Type z}

structure System (L : Language.{u}) (P : Type v) (V : Type w)
    extends Structure L V where
  part : V → P
  relTransversal :
    ∀ R x, rel R x → ∀ i j, part (x i) = part (x j) → x i = x j
  funcTransversal :
    ∀ F x y z, y ∈ func F x → z ∈ func F x →
      part y = part z → y = z

def transversal (A : Structure L P) : System L P P where
  toStructure := A
  part := id
  relTransversal := fun _ _ _ _ _ h => h
  funcTransversal := fun _ _ _ _ _ _ h => h

structure Embedding (A : System L P V) (B : System L P W)
    extends Structure.Embedding A.toStructure B.toStructure where
  map_part : ∀ x, B.part (toFun x) = A.part x

instance {A : System L P V} {B : System L P W} :
    CoeFun (Embedding A B) (fun _ => V → W) :=
  ⟨fun f => f.toEmbedding.toFun⟩

namespace Embedding

variable {A : System L P V} {B : System L P W}

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  exact Structure.Embedding.ext h

def id (A : System L P V) : Embedding A A where
  toEmbedding := Structure.Embedding.id A.toStructure
  map_part := fun _ => rfl

def comp {X : Type*} {C : System L P X}
    (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toEmbedding := g.toEmbedding.comp f.toEmbedding
  map_part x := (g.map_part (f x)).trans (f.map_part x)

@[simp] theorem comp_apply {X : Type*} {C : System L P X}
    (g : Embedding B C) (f : Embedding A B) (x : V) :
    g.comp f x = g (f x) := rfl

instance [Finite V] [Finite W] : Finite (Embedding A B) :=
  Finite.of_injective (fun f => f.toEmbedding)
    (fun _ _ h => ext (fun x =>
      congrArg (fun e : Structure.Embedding _ _ => e x) h))

end Embedding

def Arrow (A : System L P V) (B : System L P W)
    {X : Type*} (C : System L P X) (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C,
    ∀ e₁ e₂ : Embedding A B, χ (f.comp e₁) = χ (f.comp e₂)

/-- Projection preserves the full structure.  Relation reflection on
irreducibles is tracked separately by the relational reduct during the
transition to the full homomorphism-embedding API. -/
def System.ProjectionHom (B : System L P V) (A : Structure L P) : Prop :=
  B.toStructure.IsHomomorphism A B.part

end StructuralRamsey.FunctionalPartite

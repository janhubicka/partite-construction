import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Full genuine partial Option(Set) embeddings form a compositional API

To transport the verified relational Ramsey arrow into genuinely
partial-function embeddings, full maps must compose on the SAME
original vertex carrier, reflecting both undefined and defined-empty
values.

A full partial embedding preserves the entire Option(Set) fibre
under set image, so composition follows from composition of image
sets and the functorial law of Option.map. Unlike the original-2019
positive partial homomorphism, this FULL map reflects source
undefinedness and is intended for protected A- and B-copies.

The proof applies to multivalued functions, repeated inputs and
nullary functions, with no transversality or finite-carrier
assumption. No generated closure or weak source carrier is changed.
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}}
variable {U : Type v} {V : Type w} {W : Type z}
variable {A : PartialSetStructure L U}
variable {B : PartialSetStructure L V}
variable {C : PartialSetStructure L W}

/-- The identity full embedding preserves the entire Option(Set)
value, including none and some empty. -/
def id (A : PartialSetStructure L U) : Embedding A A where
  toFun := _root_.id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    rfl
  map_func := by
    intro F xs
    change (A.func F xs).map (Structure.imageSet _root_.id) =
      A.func F (_root_.id ∘ xs)
    simp only [Function.id_comp]
    cases A.func F xs with
    | none => rfl
    | some T =>
        change some (Structure.imageSet _root_.id T) = some T
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨x, hx, rfl⟩

/-- Image sets compose exactly, including empty source values. -/
theorem imageSet_comp
    (f : U → V) (g : V → W) (S : Set U) :
    Structure.imageSet (g ∘ f) S =
      Structure.imageSet g (Structure.imageSet f S) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨f x, ⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨v,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,rfl⟩

/-- Full partial-function embeddings compose, reflecting independent
function domains as well as every complete output fibre. -/
def comp (g : Embedding B C) (f : Embedding A B) :
    Embedding A C where
  toFun := g.toFun ∘ f.toFun
  injective := g.injective.comp f.injective
  map_rel_iff := by
    intro R xs
    calc
      C.rel R ((g.toFun ∘ f.toFun) ∘ xs) ↔
          B.rel R (f.toFun ∘ xs) :=
        g.map_rel_iff R (f.toFun ∘ xs)
      _ ↔ A.rel R xs := f.map_rel_iff R xs
  map_func := by
    intro F xs
    have hMap :
        (A.func F xs).map (Structure.imageSet (g.toFun ∘ f.toFun)) =
        ((A.func F xs).map (Structure.imageSet f.toFun)).map
          (Structure.imageSet g.toFun) := by
      cases A.func F xs with
      | none => rfl
      | some T =>
          change some (Structure.imageSet (g.toFun ∘ f.toFun) T) =
            some (Structure.imageSet g.toFun
              (Structure.imageSet f.toFun T))
          exact congrArg some (imageSet_comp f.toFun g.toFun T)
    calc
      (A.func F xs).map (Structure.imageSet (g.toFun ∘ f.toFun)) =
          ((A.func F xs).map (Structure.imageSet f.toFun)).map
            (Structure.imageSet g.toFun) := hMap
      _ = (B.func F (f.toFun ∘ xs)).map
          (Structure.imageSet g.toFun) :=
        congrArg (Option.map (Structure.imageSet g.toFun))
          (f.map_func F xs)
      _ = C.func F ((g.toFun ∘ f.toFun) ∘ xs) :=
        g.map_func F (f.toFun ∘ xs)

end StructuralRamsey.PartialSetStructure.Embedding

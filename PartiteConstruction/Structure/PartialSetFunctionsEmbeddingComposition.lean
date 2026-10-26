import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Full genuine partial Option(Set) embeddings compose

The source-faithful genuine-partial function embedding API stores
the ENTIRE Option(Set) fibre under an injective map. Its identity
and composition preserve undefined as distinct from defined-empty.

These constructors and the extensionality lemma are needed to
transport Ramsey-arrow monochromaticity between canonical
complete-mask OLD relational embeddings and genuinely partial
functional embeddings on the exact same vertices. No weak projection
is asserted to be a FULL embedding.
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}}
variable {V : Type v} {W : Type w} {X : Type z}
variable {A : PartialSetStructure L V}
variable {B : PartialSetStructure L W}
variable {C : PartialSetStructure L X}

/-- Full Option(Set) functional embeddings are determined by their
underlying vertex map; injectivity, relations and whole-fibre equality
are proposition-valued structure fields. -/
theorem ext_toFun (e f : Embedding A B)
    (h : ∀ x, e.toFun x = f.toFun x) : e = f := by
  cases e with
  | mk eFun eInj eRel eFunc =>
    cases f with
    | mk fFun fInj fRel fFunc =>
      have heq : eFun = fFun := funext h
      cases heq
      rfl

/-- Genuinely partial full embeddings COMPOSE. This does not collapse
none to some empty: Option.map preserves the definedness constructor,
and imageSet of imageSet equals imageSet of the composed vertex map. -/
def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toFun := g.toFun ∘ f.toFun
  injective := g.injective.comp f.injective
  map_rel_iff := by
    intro R xs
    calc
      C.rel R ((g.toFun ∘ f.toFun) ∘ xs) ↔
          C.rel R (g.toFun ∘ (f.toFun ∘ xs)) := Iff.rfl
      _ ↔ B.rel R (f.toFun ∘ xs) :=
        g.map_rel_iff R (f.toFun ∘ xs)
      _ ↔ A.rel R xs := f.map_rel_iff R xs
  map_func := by
    classical
    intro F xs
    have hImage (U : Set V) :
        imageSet (g.toFun ∘ f.toFun) U =
          imageSet g.toFun (imageSet f.toFun U) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨f.toFun x, ⟨x,hx,rfl⟩, rfl⟩
      · rintro ⟨v, ⟨x,hx,rfl⟩, rfl⟩
        exact ⟨x,hx,rfl⟩
    have hOption :
        (A.func F xs).map (imageSet (g.toFun ∘ f.toFun)) =
        ((A.func F xs).map (imageSet f.toFun)).map
          (imageSet g.toFun) := by
      cases hv : A.func F xs with
      | none => rfl
      | some U =>
          change some (imageSet (g.toFun ∘ f.toFun) U) =
            some (imageSet g.toFun (imageSet f.toFun U))
          exact congrArg some (hImage U)
    calc
      (A.func F xs).map (imageSet (g.toFun ∘ f.toFun)) =
          ((A.func F xs).map (imageSet f.toFun)).map
            (imageSet g.toFun) := hOption
      _ = (B.func F (f.toFun ∘ xs)).map
            (imageSet g.toFun) := by rw [f.map_func F xs]
      _ = C.func F (g.toFun ∘ (f.toFun ∘ xs)) :=
        g.map_func F (f.toFun ∘ xs)
      _ = C.func F ((g.toFun ∘ f.toFun) ∘ xs) := rfl

end StructuralRamsey.PartialSetStructure.Embedding

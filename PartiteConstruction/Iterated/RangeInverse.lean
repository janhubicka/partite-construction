import PartiteConstruction.Iterated.LocalTreeLike

/-! # Inverting an embedding on its finite image

For grouping final sparsening roots by support inside the base, an embedding
of a finite root into the base must be re-read as an isomorphism onto its
image support.  This file packages the inverse embedding into the source.
-/
namespace StructuralRamsey.RelStructure.Embedding

universe u v
variable {L : RelLanguage.{u}}
variable {V W : Type v}
variable {A : RelStructure L V} {B : RelStructure L W}

/-- The inverse embedding from the induced range of an embedding back to its
source. -/
noncomputable def rangeInverse (e : Embedding A B) :
    Embedding (B.induce (Set.range e)) A where
  toFun z := Classical.choose z.2
  injective := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = e (Classical.choose x.2) := (Classical.choose_spec x.2).symm
      _ = e (Classical.choose y.2) := congrArg e hxy
      _ = y.1 := Classical.choose_spec y.2
  map_rel_iff := by
    intro R x
    let q : Fin (L.arity R) → V := fun i => Classical.choose (x i).2
    have heq : e ∘ q = Subtype.val ∘ x := by
      funext i
      exact Classical.choose_spec (x i).2
    calc
      A.rel R q ↔ B.rel R (e ∘ q) := (e.map_rel_iff R q).symm
      _ ↔ B.rel R (Subtype.val ∘ x) := by rw [heq]
      _ ↔ (B.induce (Set.range e)).rel R x := Iff.rfl

@[simp] theorem rangeInverse_apply (e : Embedding A B)
    (z : Set.range e) :
    e (e.rangeInverse z) = z.1 :=
  Classical.choose_spec z.2

/-- The original embedding and its range inverse are mutually inverse after
restricting the codomain to the range. -/
theorem rangeInverse_left (e : Embedding A B) (x : V) :
    e.rangeInverse ⟨e x, ⟨x, rfl⟩⟩ = x := by
  apply e.injective
  exact e.rangeInverse_apply ⟨e x, ⟨x, rfl⟩⟩

end StructuralRamsey.RelStructure.Embedding

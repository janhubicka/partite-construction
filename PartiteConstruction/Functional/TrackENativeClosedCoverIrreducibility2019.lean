import PartiteConstruction.Structure.IrreducibleHomImage

/-!
# Track E: a native irreducible cannot admit a proper closed free cover

Abstract, genuinely set-valued native lemma used by Appendix A. Both sides
must be closed under all functions. Every original relation tuple and
every positive function incidence is localized to one side. Construct
the LITERAL free amalgam of the two induced full functional sides and
use universal irreducibility of the source. Empty fibres and nullary
relations are handled without additional assumptions.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A genuine native irreducible is not a nontrivial two-sided cover
by function-closed sets with all original incidences localized. -/
theorem Irreducible.closed_cover_of_local_incidents
    (A : Structure L V) (hIrr : A.Irreducible)
    (X Y : Set V)
    (hX : A.IsClosed X) (hY : A.IsClosed Y)
    (hCover : ∀ v : V, v ∈ X ∨ v ∈ Y)
    (hRel : ∀ R (t : Fin (L.relArity R) → V),
      A.rel R t → (∀ k, t k ∈ X) ∨ (∀ k, t k ∈ Y))
    (hFunc : ∀ F (xs : Fin (L.funcArity F) → V) (y : V),
      y ∈ A.func F xs →
        ((∀ i, xs i ∈ X) ∧ y ∈ X) ∨
        ((∀ i, xs i ∈ Y) ∧ y ∈ Y)) :
    (∀ v : V, v ∈ X) ∨ (∀ v : V, v ∈ Y) := by
  classical
  let Z : Set V := X ∩ Y
  have hZ : A.IsClosed Z := by
    intro F xs hxs y hy
    exact ⟨hX F xs (fun i => (hxs i).1) hy,
      hY F xs (fun i => (hxs i).2) hy⟩
  let Left : Structure L X := A.induce X hX
  let Right : Structure L Y := A.induce Y hY
  let Root : Structure L Z := A.induce Z hZ
  let iL : Embedding Left A := inclusion A X hX
  let iR : Embedding Right A := inclusion A Y hY
  let sL : Embedding Root Left := {
    toFun := fun z => ⟨z.1, z.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : X => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyY : y.1 ∈ Y :=
          hY F (Subtype.val ∘ xs)
            (fun i => (xs i).2.2) hy
        exact ⟨⟨y.1, ⟨y.2, hyY⟩⟩, hy, rfl⟩
  }
  let sR : Embedding Root Right := {
    toFun := fun z => ⟨z.1, z.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Y => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyX : y.1 ∈ X :=
          hX F (Subtype.val ∘ xs)
            (fun i => (xs i).2.1) hy
        exact ⟨⟨y.1, ⟨hyX, y.2⟩⟩, hy, rfl⟩
  }
  have hFree : IsFreeAmalgam sL sR iL iR := by
    constructor
    · intro v
      rcases hCover v with hv | hv
      · exact Or.inl ⟨⟨v, hv⟩, rfl⟩
      · exact Or.inr ⟨⟨v, hv⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have he : a.1 = b.1 := hab
        have haY : a.1 ∈ Y := by rw [he]; exact b.2
        refine ⟨⟨a.1, ⟨a.2, haY⟩⟩, rfl, ?_⟩
        exact Subtype.ext he.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R t
      constructor
      · intro ht
        rcases hRel R t ht with hL | hR
        · exact Or.inl ⟨fun k => ⟨t k, hL k⟩, ht, rfl⟩
        · exact Or.inr ⟨fun k => ⟨t k, hR k⟩, ht, rfl⟩
      · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact ht
        · exact ht
    · intro F xs y
      constructor
      · intro hy
        rcases hFunc F xs y hy with ⟨hArgs, hyX⟩ | ⟨hArgs, hyY⟩
        · exact Or.inl ⟨fun i => ⟨xs i, hArgs i⟩,
            ⟨y, hyX⟩, hy, rfl, rfl⟩
        · exact Or.inr ⟨fun i => ⟨xs i, hArgs i⟩,
            ⟨y, hyY⟩, hy, rfl, rfl⟩
      · rintro (⟨xs, y, hy, hxs, hvalue⟩ |
          ⟨xs, y, hy, hxs, hvalue⟩)
        · subst xs
          subst y
          exact hy
        · subst xs
          subst y
          exact hy
  rcases hIrr hFree (Embedding.id A) with hLeft | hRight
  · left
    intro v
    obtain ⟨x, hx⟩ := hLeft v
    change v = x.1 at hx
    rw [hx]
    exact x.2
  · right
    intro v
    obtain ⟨y, hy⟩ := hRight v
    change v = y.1 at hy
    rw [hy]
    exact y.2

end StructuralRamsey.Structure

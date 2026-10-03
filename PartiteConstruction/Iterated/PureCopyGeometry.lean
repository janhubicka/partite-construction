import PartiteConstruction.Iterated.AttachmentDecompose

/-! # Geometry of an ambient irreducible copy versus one attached copy

In a simultaneous free attachment, an irreducible ambient structure lies in
the core or in one attached copy.  Relative to a fixed attached copy i, this
gives a sharper dichotomy: either the whole ambient irreducible copy lies in
copy i, or every point where it meets copy i belongs to the glued support.

This is the geometric fact needed in the pure-copy branch of the iterated
Picture argument.
-/
namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W I : Type v}
variable {Control : RelStructure L UA}
variable {Base : RelStructure L VB}
variable {Core : RelStructure L W}
variable {S : Set VB}
variable {f : I → Embedding (Base.induce S) Core}

/-- Relative to one fixed attached copy, an ambient irreducible copy is
either wholly in that copy or meets it only along the support. -/
theorem irreducible_copy_or_intersection_in_support
    (hControl : Control.Irreducible)
    (γ : Embedding Control (attach Base S Core f))
    (i : I) :
    (∀ a : UA, ∃ b : VB, γ a = copyMap Base S Core f i b) ∨
    (∀ a : UA, ∀ b : VB,
      γ a = copyMap Base S Core f i b → b ∈ S) := by
  classical
  let Rng : Set (Vertex S (W := W) (I := I)) := Set.range γ
  have hRng : ((attach Base S Core f).induce Rng).Irreducible :=
    hControl.range_embedding γ
  rcases irreducible_core_or_copy
      (B := Base) (S := S) (D := Core) (f := f) Rng hRng with
    hcore | ⟨j, hcopy⟩
  · right
    intro a b hab
    let z : Rng := ⟨γ a, ⟨a, rfl⟩⟩
    obtain ⟨w, hw⟩ := hcore z
    apply mem_of_copyMap_eq_inl
      (B := Base) (S := S) (D := Core) (f := f)
    calc
      copyMap Base S Core f i b = γ a := hab.symm
      _ = Sum.inl w := hw
  · by_cases hji : j = i
    · subst j
      left
      intro a
      let z : Rng := ⟨γ a, ⟨a, rfl⟩⟩
      exact hcopy z
    · right
      intro a b hab
      by_contra hb
      let z : Rng := ⟨γ a, ⟨a, rfl⟩⟩
      obtain ⟨b', hb'⟩ := hcopy z
      have heq :
          copyMap Base S Core f i b =
            copyMap Base S Core f j b' := by
        calc
          copyMap Base S Core f i b = γ a := hab.symm
          _ = copyMap Base S Core f j b' := hb'
      have hij : i = j :=
        index_eq_of_outside (B := Base) (D := Core) (f := f) hb heq
      exact hji hij.symm

end StructuralRamsey.RelStructure.Attachment
